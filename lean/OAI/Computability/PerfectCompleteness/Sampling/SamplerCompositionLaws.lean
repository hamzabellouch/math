import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerReplayTransportLemmas
import OAI.Computability.PerfectCompleteness.Sampling.SamplerComposition

namespace OAI

section

namespace PerfectCompleteness.SamplerComposition

open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler
open UniqueGamesTheorem.Foundations.Games

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m k : Nat}
variable (𝕜 : Type w) [Field 𝕜]

instance expansionSpaceNonempty (repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (A : Slots branch n → Type u) (j : DrawIndex repeats p) :
    Nonempty (ExpansionSpace 𝕜 repeats p q A j) :=
  ⟨zeroFactor 𝕜 repeats p q A j⟩

instance expandedTapeNonempty (repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (A : Slots branch n → Type u) :
    Nonempty (ExpandedTape 𝕜 repeats p q A) :=
  ⟨zeroExpandedTape 𝕜 repeats p q A⟩

variable [Finite 𝕜]

theorem expansionSpace_finite (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u),
      (∀ s, Finite (A s)) → ∀ j : DrawIndex repeats p,
        Finite (ExpansionSpace 𝕜 repeats p q A j) := by
  induction p with
  | refl n =>
      intro q A hA j
      let : ∀ s, Finite (A s) := hA
      let : ∀ d : DrawIndex repeats q, Fintype (DrawSpace 𝕜 repeats q A d) :=
        fun d => drawSpaceFintype 𝕜 repeats q A d
      change Finite (RecursiveSampler.Tape 𝕜 repeats q A)
      infer_instance
  | @step n m i p ih =>
      intro q A hA j
      cases j with
      | inl j =>
          let : ∀ s, Finite (childFamily A j.val s) := fun s => hA (j.val, s)
          change Finite (squareSpace (space 𝕜 branch n (childFamily A j.val)))
          infer_instance
      | inr j =>
          exact ih q (childFamily A i) (fun s => hA (i, s)) j.2

instance expansionSpaceFinite (repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (A : Slots branch n → Type u) [∀ s, Finite (A s)]
    (j : DrawIndex repeats p) : Finite (ExpansionSpace 𝕜 repeats p q A j) :=
  expansionSpace_finite 𝕜 repeats p q A (fun _ => inferInstance) j

instance expansionSpaceFintype (repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (A : Slots branch n → Type u) [∀ s, Finite (A s)]
    (j : DrawIndex repeats p) : Fintype (ExpansionSpace 𝕜 repeats p q A j) :=
  Fintype.ofFinite _

instance expandedTapeFintype (repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    Fintype (ExpandedTape 𝕜 repeats p q A) :=
  @Pi.instFintype (DrawIndex repeats p) (ExpansionSpace 𝕜 repeats p q A)
    (drawIndexDecidableEq repeats p) (drawIndexFintype repeats p)
    (fun j => expansionSpaceFintype 𝕜 repeats p q A j)

def expandedTapeLaw (repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    FiniteDistribution (ExpandedTape 𝕜 repeats p q A) := by
  letI : ∀ j : DrawIndex repeats p, Fintype (ExpansionSpace 𝕜 repeats p q A j) :=
    fun j => expansionSpaceFintype 𝕜 repeats p q A j
  letI : ∀ j : DrawIndex repeats p, Nonempty (ExpansionSpace 𝕜 repeats p q A j) :=
    fun j => expansionSpaceNonempty 𝕜 repeats p q A j
  exact FiniteProduct.law (fun j => FiniteDistribution.uniform (ExpansionSpace 𝕜 repeats p q A j))

theorem expandedTapeLaw_eq_uniform (repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    expandedTapeLaw 𝕜 repeats p q A = FiniteDistribution.uniform (ExpandedTape 𝕜 repeats p q A) := by
  let : ∀ j : DrawIndex repeats p, Fintype (ExpansionSpace 𝕜 repeats p q A j) :=
    fun j => expansionSpaceFintype 𝕜 repeats p q A j
  let : ∀ j : DrawIndex repeats p, Nonempty (ExpansionSpace 𝕜 repeats p q A j) :=
    fun j => expansionSpaceNonempty 𝕜 repeats p q A j
  exact UniformLinearImage.law_uniform

theorem expand_tapeLaw (repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    (tapeLaw 𝕜 repeats (p.append q) A).pushforward (expandEquiv 𝕜 repeats p q A) =
      expandedTapeLaw 𝕜 repeats p q A := by
  rw [tapeLaw_eq_uniform, expandedTapeLaw_eq_uniform,
    ← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (expandEquiv 𝕜 repeats p q A)

def factorLaw (repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (A : Slots branch n → Type u) [∀ s, Finite (A s)]
    (j : DrawIndex repeats p) : FiniteDistribution (DrawSpace 𝕜 repeats p A j) :=
  (FiniteDistribution.uniform (ExpansionSpace 𝕜 repeats p q A j)).pushforward
    (collapseFactor 𝕜 repeats p q A j)

theorem collapseExpanded_expandedTapeLaw (repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    (expandedTapeLaw 𝕜 repeats p q A).pushforward (collapseExpanded 𝕜 repeats p q A) =
      FiniteProduct.law (factorLaw 𝕜 repeats p q A) := by
  let : ∀ j : DrawIndex repeats p, Fintype (ExpansionSpace 𝕜 repeats p q A j) :=
    fun j => expansionSpaceFintype 𝕜 repeats p q A j
  let : ∀ j : DrawIndex repeats p, Nonempty (ExpansionSpace 𝕜 repeats p q A j) :=
    fun j => expansionSpaceNonempty 𝕜 repeats p q A j
  exact FiniteProduct.pushforward_map _ (collapseFactor 𝕜 repeats p q A)

theorem collapseSuffix_tapeLaw (repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    (tapeLaw 𝕜 repeats (p.append q) A).pushforward (collapseSuffix 𝕜 repeats p q A) =
      FiniteProduct.law (factorLaw 𝕜 repeats p q A) := by
  calc
    _ = ((tapeLaw 𝕜 repeats (p.append q) A).pushforward
        (expandEquiv 𝕜 repeats p q A)).pushforward (collapseExpanded 𝕜 repeats p q A) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := by rw [expand_tapeLaw, collapseExpanded_expandedTapeLaw]

theorem law_append (repeats : Nat → Nat) (p : Path branch n m)
    (q : Path branch m k) (A : Slots branch n → Type u) [∀ s, Finite (A s)]
    [Fintype (space 𝕜 branch n A)] :
    RecursiveSampler.law 𝕜 repeats (p.append q) A =
      (FiniteProduct.law (factorLaw 𝕜 repeats p q A)).pushforward
        (RecursiveSampler.evaluate 𝕜 repeats p A) := by
  calc
    _ = ((tapeLaw 𝕜 repeats (p.append q) A).pushforward
        (collapseSuffix 𝕜 repeats p q A)).pushforward
          (RecursiveSampler.evaluate 𝕜 repeats p A) := by
      rw [FiniteDistribution.pushforward_comp]
      unfold RecursiveSampler.law
      congr 1
      funext t
      exact (evaluate_collapseSuffix 𝕜 repeats p q A t).symm
    _ = _ := by rw [collapseSuffix_tapeLaw]

end
end PerfectCompleteness.SamplerComposition

end

end OAI
