import OAI.Computability.PerfectCompleteness.Repetition.CleanConditioning
import OAI.Computability.PerfectCompleteness.Sampling.RecordSeedSamplingLemmas
import OAI.Computability.PerfectCompleteness.Sampling.UniformChildSum
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI

section

namespace PerfectCompleteness.CutSamplerRefinement

open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

def RefinedSpace (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → (A : Slots branch n → Type u) →
      DrawIndex repeats p → Type (max u w)
  | 0, _, .refl _, A, _ => space 𝕜 branch 0 A
  | n + 1, _, .refl _, A, _ =>
      (i : Fin (branch n)) → squareSpace (space 𝕜 branch n (childFamily A i))
  | n + 1, _, .step i p, A, j =>
      match j with
      | Sum.inl j => squareSpace (space 𝕜 branch n (childFamily A j.val))
      | Sum.inr j => RefinedSpace 𝕜 repeats p (childFamily A i) j.2

def zeroFactor (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → (A : Slots branch n → Type u) →
      (j : DrawIndex repeats p) → RefinedSpace 𝕜 repeats p A j
  | 0, _, .refl _, A, _ => (0 : space 𝕜 branch 0 A)
  | n + 1, _, .refl _, A, _ =>
      fun i => (0 : squareSpace (space 𝕜 branch n (childFamily A i)))
  | n + 1, _, .step i p, A, j =>
      match j with
      | Sum.inl j => (0 : squareSpace (space 𝕜 branch n (childFamily A j.val)))
      | Sum.inr j => zeroFactor 𝕜 repeats p (childFamily A i) j.2

instance refinedNonempty (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) (j : DrawIndex repeats p) :
    Nonempty (RefinedSpace 𝕜 repeats p A j) := ⟨zeroFactor 𝕜 repeats p A j⟩

theorem refined_finite (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u), (∀ s, Finite (A s)) →
      ∀ j : DrawIndex repeats p, Finite (RefinedSpace 𝕜 repeats p A j) := by
  induction p with
  | refl n =>
      intro A hA j
      let : ∀ s, Finite (A s) := hA
      cases n with
      | zero =>
          change Finite (space 𝕜 branch 0 A)
          infer_instance
      | succ n =>
          change Finite ((i : Fin (branch n)) →
            squareSpace (space 𝕜 branch n (childFamily A i)))
          let : ∀ i : Fin (branch n),
              Finite (squareSpace (space 𝕜 branch n (childFamily A i))) := fun i => by
            let : ∀ s, Finite ((childFamily A i) s) := fun s => hA (i, s)
            infer_instance
          infer_instance
  | @step n m i p ih =>
      intro A hA j
      cases j with
      | inl j =>
          let : ∀ s, Finite ((childFamily A j.val) s) := fun s => hA (j.val, s)
          change Finite (squareSpace (space 𝕜 branch n (childFamily A j.val)))
          infer_instance
      | inr j =>
          exact ih (childFamily A i) (fun s => hA (i, s)) j.2

instance refinedFinite (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] (j : DrawIndex repeats p) :
    Finite (RefinedSpace 𝕜 repeats p A j) :=
  refined_finite 𝕜 repeats p A (fun _ => inferInstance) j

instance refinedFintype (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] (j : DrawIndex repeats p) :
    Fintype (RefinedSpace 𝕜 repeats p A j) := Fintype.ofFinite _

def collapseFactor (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → (A : Slots branch n → Type u) →
      (j : DrawIndex repeats p) → RefinedSpace 𝕜 repeats p A j → DrawSpace 𝕜 repeats p A j
  | 0, _, .refl _, _, _, x => x
  | _ + 1, _, .refl _, A, _, x => UniformChildSum.recursiveSum A x
  | _ + 1, _, .step i p, A, j, x =>
      match j with
      | Sum.inl _ => x
      | Sum.inr j => collapseFactor 𝕜 repeats p (childFamily A i) j.2 x

abbrev Tape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) :=
  (j : DrawIndex repeats p) → RefinedSpace 𝕜 repeats p A j

def collapse (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) :
    Tape 𝕜 repeats p A → RecursiveSampler.Tape 𝕜 repeats p A :=
  fun x j => collapseFactor 𝕜 repeats p A j (x j)

def tapeLaw (𝕜 : Type w) [Field 𝕜] [Finite 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    FiniteDistribution (Tape 𝕜 repeats p A) :=
  FiniteProduct.law (fun j => FiniteDistribution.uniform (RefinedSpace 𝕜 repeats p A j))

private theorem pushforward_identity {Ω : Type*} [Fintype Ω] (μ : FiniteDistribution Ω) :
    μ.pushforward (fun x => x) = μ := by
  change μ.pushforward (Equiv.refl Ω) = μ
  rw [FiniteDistribution.pushforward_equiv]
  exact FiniteDistribution.eq_of_weight_eq (fun _ => rfl)

theorem collapseFactor_uniform (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u) [∀ s, Finite (A s)] (j : DrawIndex repeats p),
      (FiniteDistribution.uniform (RefinedSpace 𝕜 repeats p A j)).pushforward
        (collapseFactor 𝕜 repeats p A j) =
      FiniteDistribution.uniform (DrawSpace 𝕜 repeats p A j) := by
  induction p with
  | refl n =>
      intro A hA j
      cases n with
      | zero =>
          let : ∀ s, Finite (A s) := hA
          let : Fintype (space 𝕜 branch 0 A) := Fintype.ofFinite _
          change (FiniteDistribution.uniform (space 𝕜 branch 0 A)).pushforward
              (fun x => x) = FiniteDistribution.uniform (space 𝕜 branch 0 A)
          exact pushforward_identity _
      | succ n =>
          let : Fintype ((i : Fin (branch n)) →
              squareSpace (space 𝕜 branch n (childFamily A i))) :=
            refinedFintype 𝕜 repeats (.refl (n + 1)) A j
          let : Fintype (space 𝕜 branch (n + 1) A) :=
            RecursiveSampler.drawSpaceFintype 𝕜 repeats (.refl (n + 1)) A j
          exact UniformLinearImage.uniform_pushforward_linearMap
            (UniformChildSum.recursiveSum (𝕜 := 𝕜) A)
            (UniformChildSum.recursiveSum_surjective (𝕜 := 𝕜) A)
  | @step n m i p ih =>
      intro A hA j
      cases j with
      | inl j =>
          let : ∀ s, Finite ((childFamily A j.val) s) := fun s => hA (j.val, s)
          let : Fintype (squareSpace (space 𝕜 branch n (childFamily A j.val))) :=
            Fintype.ofFinite _
          change (FiniteDistribution.uniform
              (squareSpace (space 𝕜 branch n (childFamily A j.val)))).pushforward
              (fun x => x) = FiniteDistribution.uniform
                (squareSpace (space 𝕜 branch n (childFamily A j.val)))
          apply FiniteDistribution.eq_of_weight_eq
          intro x
          simp [FiniteDistribution.pushforward]
      | inr j =>
          let : ∀ s, Finite ((childFamily A i) s) := fun s => hA (i, s)
          exact ih (childFamily A i) j.2

theorem collapse_tapeLaw (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    (tapeLaw 𝕜 repeats p A).pushforward (collapse 𝕜 repeats p A) =
      RecursiveSampler.tapeLaw 𝕜 repeats p A := by
  unfold tapeLaw collapse
  rw [CleanConditioning.pushforward_law]
  simp_rw [collapseFactor_uniform]
  rfl

def evaluate (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) (x : Tape 𝕜 repeats p A) :
    space 𝕜 branch n A :=
  RecursiveSampler.evaluate 𝕜 repeats p A (collapse 𝕜 repeats p A x)

theorem evaluate_law (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] [Fintype (space 𝕜 branch n A)] :
    (tapeLaw 𝕜 repeats p A).pushforward (evaluate 𝕜 repeats p A) =
      RecursiveSampler.law 𝕜 repeats p A := by
  change (tapeLaw 𝕜 repeats p A).pushforward
    ((RecursiveSampler.evaluate 𝕜 repeats p A) ∘ collapse 𝕜 repeats p A) = _
  calc
    _ = ((tapeLaw 𝕜 repeats p A).pushforward (collapse 𝕜 repeats p A)).pushforward
        (RecursiveSampler.evaluate 𝕜 repeats p A) :=
      (FiniteDistribution.pushforward_comp (tapeLaw 𝕜 repeats p A)
        (collapse 𝕜 repeats p A) (RecursiveSampler.evaluate 𝕜 repeats p A)).symm
    _ = _ := by
      rw [collapse_tapeLaw]
      rfl

end
end PerfectCompleteness.CutSamplerRefinement

end

end OAI
