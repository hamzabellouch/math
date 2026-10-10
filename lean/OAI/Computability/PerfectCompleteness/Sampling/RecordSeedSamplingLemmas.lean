import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import OAI.Computability.PerfectCompleteness.Construction.DescendantSpacesLemmas
import OAI.Computability.PerfectCompleteness.Decoding.DependentDecoderSampling
import OAI.Computability.PerfectCompleteness.Sampling.RecursiveSamplerLaws

namespace OAI


namespace PerfectCompleteness.RecordSeedSampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {X R : Type*} [Fintype X] [Fintype R] [DecidableEq R]
  {Seed : R → Type*} [∀ r, Fintype (Seed r)]

def freshLaw (P : FiniteDistribution X) (record : X → R)
    (kernel : (r : R) → FiniteDistribution (Seed r)) :
    FiniteDistribution (Σ x : X, Seed (record x)) :=
  CompletionSoundness.sigmaLaw P (fun x => kernel (record x))

theorem probability_eq_table_mean (P : FiniteDistribution X) (record : X → R)
    (kernel : (r : R) → FiniteDistribution (Seed r))
    (event : (x : X) → Seed (record x) → Bool) :
    (freshLaw P record kernel).probability (fun z => event z.1 z.2) =
      (FiniteProduct.law kernel).expectation
        (fun table => P.probability (fun x => event x (table (record x)))) := by
  rw [freshLaw, CompletionSoundness.sigmaLaw_probability]
  calc
    _ = P.expectation (fun x => (FiniteProduct.law kernel).probability
        (fun table => event x (table (record x)))) := by
      apply FiniteDistribution.expectation_congr
      intro x
      have h := FiniteDistribution.probability_pushforward
        (FiniteProduct.law kernel) (fun table => table (record x)) (event x)
      rw [FiniteProduct.eval_pushforward] at h
      exact h
    _ = P.expectation (fun x => (FiniteProduct.law kernel).expectation
        (fun table => if event x (table (record x)) then 1 else 0)) := by
      simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
        mul_ite, mul_one, mul_zero]
    _ = (FiniteProduct.law kernel).expectation (fun table => P.expectation
        (fun x => if event x (table (record x)) then 1 else 0)) :=
      FiniteDistribution.expectation_comm P (FiniteProduct.law kernel) _
    _ = _ := by
      simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
        mul_ite, mul_one, mul_zero]

theorem supported_row (kernel : (r : R) → FiniteDistribution (Seed r))
    (table : (r : R) → Seed r)
    (hs : (FiniteProduct.law kernel).weight table ≠ 0) (r : R) :
    (kernel r).weight (table r) ≠ 0 := by
  intro hr
  exact hs (Finset.prod_eq_zero (Finset.mem_univ r) hr)

theorem probability_supported_guard (P : FiniteDistribution X) (event : X → Bool) :
    P.probability (fun x => decide (P.weight x ≠ 0) && event x) = P.probability event := by
  unfold FiniteDistribution.probability
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P.weight x = 0
  · simp only [hx, ne_eq, not_true_eq_false, decide_false, Bool.false_and,
      ite_self]
  · simp only [decide_eq_true hx, Bool.true_and]

theorem probability_le_of_supported_tables (P : FiniteDistribution X) (record : X → R)
    (kernel : (r : R) → FiniteDistribution (Seed r))
    (event : (x : X) → Seed (record x) → Bool) (bound : ℝ)
    (hbound : ∀ table, (FiniteProduct.law kernel).weight table ≠ 0 →
      P.probability (fun x => decide (P.weight x ≠ 0) && event x (table (record x))) ≤ bound) :
    (freshLaw P record kernel).probability (fun z => event z.1 z.2) ≤ bound := by
  rw [probability_eq_table_mean]
  apply DecoderTableAdmissibility.expectation_le_of_support
  intro table hs
  rw [← probability_supported_guard P (fun x => event x (table (record x)))]
  exact hbound table hs

end
end PerfectCompleteness.RecordSeedSampling



namespace PerfectCompleteness.RecursiveSampler

open PointwiseSpaces RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

universe u w

variable {branch : Nat → Nat} {n m : Nat}

abbrev OffPath (i : Fin (branch n)) := {j : Fin (branch n) // j ≠ i}

def DrawIndex (repeats : Nat → Nat) : {n m : Nat} → Path branch n m → Type
  | _, _, .refl _ => Unit
  | n + 1, _, .step i p =>
      OffPath i ⊕ ((Fin (repeats (n + 1)) × Bool) × DrawIndex repeats p)

noncomputable instance drawIndexFintype (repeats : Nat → Nat) (p : Path branch n m) :
    Fintype (DrawIndex repeats p) := by
  induction p with
  | refl n => exact inferInstanceAs (Fintype Unit)
  | @step n m i p ih =>
      letI : Fintype (DrawIndex repeats p) := ih
      exact inferInstanceAs (Fintype
        (OffPath i ⊕ ((Fin (repeats (n + 1)) × Bool) × DrawIndex repeats p)))

noncomputable instance drawIndexDecidableEq (repeats : Nat → Nat) (p : Path branch n m) :
    DecidableEq (DrawIndex repeats p) := by
  induction p with
  | refl n => exact inferInstanceAs (DecidableEq Unit)
  | @step n m i p ih =>
      letI : DecidableEq (DrawIndex repeats p) := ih
      exact inferInstanceAs (DecidableEq
        (OffPath i ⊕ ((Fin (repeats (n + 1)) × Bool) × DrawIndex repeats p)))

variable (𝕜 : Type w) [Field 𝕜]

def DrawSpace (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → (A : Slots branch n → Type u) →
      DrawIndex repeats p → Type (max u w)
  | n, _, .refl _, A, _ => space 𝕜 branch n A
  | n + 1, _, .step i p, A, j =>
      match j with
      | Sum.inl j => squareSpace (space 𝕜 branch n (childFamily A j.val))
      | Sum.inr j => DrawSpace 𝕜 repeats p (childFamily A i) j.2

abbrev Tape (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) :=
  (j : DrawIndex repeats p) → DrawSpace 𝕜 repeats p A j

def zeroDraw (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → (A : Slots branch n → Type u) →
      (j : DrawIndex repeats p) → DrawSpace 𝕜 repeats p A j
  | n, _, .refl _, A, _ => (0 : space 𝕜 branch n A)
  | n + 1, _, .step i p, A, j =>
      match j with
      | Sum.inl j => (0 : squareSpace (space 𝕜 branch n (childFamily A j.val)))
      | Sum.inr j => zeroDraw 𝕜 repeats p (childFamily A i) j.2

def zeroTape (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) : Tape 𝕜 repeats p A :=
  zeroDraw 𝕜 repeats p A

instance drawSpaceNonempty (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) (j : DrawIndex repeats p) :
    Nonempty (DrawSpace 𝕜 repeats p A j) :=
  ⟨zeroDraw 𝕜 repeats p A j⟩

instance tapeNonempty (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) : Nonempty (Tape 𝕜 repeats p A) :=
  ⟨zeroTape 𝕜 repeats p A⟩

theorem drawSpace_finite [Finite 𝕜] (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u), (∀ s, Finite (A s)) →
      ∀ j : DrawIndex repeats p, Finite (DrawSpace 𝕜 repeats p A j) := by
  induction p with
  | refl n =>
      intro A hA j
      let : ∀ s, Finite (A s) := hA
      change Finite (space 𝕜 branch n A)
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

instance drawSpaceFinite [Finite 𝕜] (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] (j : DrawIndex repeats p) :
    Finite (DrawSpace 𝕜 repeats p A j) :=
  drawSpace_finite 𝕜 repeats p A (fun _ => inferInstance) j

noncomputable instance drawSpaceFintype [Finite 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) [∀ s, Finite (A s)]
    (j : DrawIndex repeats p) : Fintype (DrawSpace 𝕜 repeats p A j) :=
  Fintype.ofFinite _

def subTape (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) (t : Tape 𝕜 repeats (.step i p) A)
    (h : Fin (repeats (n + 1))) (b : Bool) :
    Tape 𝕜 repeats p (childFamily A i) :=
  fun j => t (.inr ((h, b), j))

theorem recursive_locations_distinct (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n m)
    (h h' : Fin (repeats (n + 1))) (b b' : Bool)
    (j j' : DrawIndex repeats p) (hne : (h, b) ≠ (h', b')) :
    (Sum.inr ((h, b), j) : DrawIndex repeats (.step i p)) ≠
      Sum.inr ((h', b'), j') := by
  intro heq
  exact hne (congrArg Prod.fst (Sum.inr.inj heq))

noncomputable section

def combineFunction (A : Slots branch (n + 1) → Type u) (i : Fin (branch n))
    (r : Nat)
    (ordinary : (j : OffPath i) → squareSpace (space 𝕜 branch n (childFamily A j.val)))
    (left right : Fin r → space 𝕜 branch n (childFamily A i)) : Assignment A → 𝕜 :=
  (∑ j : OffPath i, pullback 𝕜 (childRestriction A j.val) (ordinary j).val) +
    ∑ h : Fin r, pullback 𝕜 (childRestriction A i) ((left h).val * (right h).val)

theorem combineFunction_mem (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (r : Nat)
    (ordinary : (j : OffPath i) → squareSpace (space 𝕜 branch n (childFamily A j.val)))
    (left right : Fin r → space 𝕜 branch n (childFamily A i)) :
    combineFunction 𝕜 A i r ordinary left right ∈ space 𝕜 branch (n + 1) A := by
  apply (space 𝕜 branch (n + 1) A).add_mem
  · apply (space 𝕜 branch (n + 1) A).sum_mem
    intro j _
    exact child_square_le_space A j.val (Submodule.mem_map_of_mem (ordinary j).property)
  · apply (space 𝕜 branch (n + 1) A).sum_mem
    intro h _
    exact child_square_le_space A i (Submodule.mem_map_of_mem
      (mul_mem_squareSpace _ (left h).property (right h).property))

def combine (A : Slots branch (n + 1) → Type u) (i : Fin (branch n)) (r : Nat)
    (ordinary : (j : OffPath i) → squareSpace (space 𝕜 branch n (childFamily A j.val)))
    (left right : Fin r → space 𝕜 branch n (childFamily A i)) :
    space 𝕜 branch (n + 1) A :=
  ⟨combineFunction 𝕜 A i r ordinary left right,
    combineFunction_mem 𝕜 A i r ordinary left right⟩

@[simp] theorem combine_zero (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (r : Nat) :
    combine 𝕜 A i r (fun _ => 0) (fun _ => 0) (fun _ => 0) = 0 := by
  apply Subtype.ext
  funext x
  simp [combine, combineFunction, PointwiseSpaces.pullback]

def evaluate (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) → (A : Slots branch n → Type u) →
      Tape 𝕜 repeats p A → space 𝕜 branch n A
  | _, _, .refl _, _, t => t ()
  | n + 1, _, .step i p, A, t =>
      combine 𝕜 A i (repeats (n + 1)) (fun j => t (.inl j))
        (fun h => evaluate 𝕜 repeats p (childFamily A i)
          (subTape 𝕜 repeats i p A t h false))
        (fun h => evaluate 𝕜 repeats p (childFamily A i)
          (subTape 𝕜 repeats i p A t h true))

@[simp] theorem evaluate_refl (repeats : Nat → Nat)
    (A : Slots branch n → Type u) (t : Tape 𝕜 repeats (.refl n) A) :
    evaluate 𝕜 repeats (.refl n) A t = t () := rfl

theorem evaluate_step (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    (t : Tape 𝕜 repeats (.step i p) A) :
    evaluate 𝕜 repeats (.step i p) A t =
      combine 𝕜 A i (repeats (n + 1)) (fun j => t (.inl j))
        (fun h => evaluate 𝕜 repeats p (childFamily A i)
          (subTape 𝕜 repeats i p A t h false))
        (fun h => evaluate 𝕜 repeats p (childFamily A i)
          (subTape 𝕜 repeats i p A t h true)) := rfl

theorem evaluate_mem (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) (t : Tape 𝕜 repeats p A) :
    (evaluate 𝕜 repeats p A t).val ∈ space 𝕜 branch n A :=
  (evaluate 𝕜 repeats p A t).property

@[simp] theorem evaluate_zeroTape (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u),
      evaluate 𝕜 repeats p A (zeroTape 𝕜 repeats p A) = 0 := by
  induction p with
  | refl n =>
      intro A
      rfl
  | @step n m i p ih =>
      intro A
      change combine 𝕜 A i (repeats (n + 1)) (fun _ => 0)
        (fun _ => evaluate 𝕜 repeats p (childFamily A i)
          (zeroTape 𝕜 repeats p (childFamily A i)))
        (fun _ => evaluate 𝕜 repeats p (childFamily A i)
          (zeroTape 𝕜 repeats p (childFamily A i))) = 0
      simp only [ih, combine_zero]

variable [Finite 𝕜]

def tapeLaw (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    FiniteDistribution (Tape 𝕜 repeats p A) :=
  FiniteProduct.law (fun j => FiniteDistribution.uniform (DrawSpace 𝕜 repeats p A j))

theorem tapeLaw_eq_uniform (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    tapeLaw 𝕜 repeats p A = FiniteDistribution.uniform (Tape 𝕜 repeats p A) :=
  UniformLinearImage.law_uniform

theorem tapeLaw_marginal (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] (j : DrawIndex repeats p) :
    (tapeLaw 𝕜 repeats p A).pushforward (fun t => t j) =
      FiniteDistribution.uniform (DrawSpace 𝕜 repeats p A j) :=
  FiniteProduct.eval_pushforward _ j

def law (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)]
    [Fintype (space 𝕜 branch n A)] : FiniteDistribution (space 𝕜 branch n A) :=
  (tapeLaw 𝕜 repeats p A).pushforward (evaluate 𝕜 repeats p A)

theorem law_refl_uniform (repeats : Nat → Nat) (A : Slots branch n → Type u)
    [∀ s, Finite (A s)] [out : Fintype (space 𝕜 branch n A)] :
    law 𝕜 repeats (.refl n) A = FiniteDistribution.uniform (space 𝕜 branch n A) := by
  have hout : out = drawSpaceFintype 𝕜 repeats (.refl n) A () := Subsingleton.elim _ _
  cases hout
  exact tapeLaw_marginal 𝕜 repeats (.refl n) A ()

theorem probability_law (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)]
    [Fintype (space 𝕜 branch n A)] (event : space 𝕜 branch n A → Bool) :
    (law 𝕜 repeats p A).probability event =
      (tapeLaw 𝕜 repeats p A).probability (fun t => event (evaluate 𝕜 repeats p A t)) :=
  FiniteDistribution.probability_pushforward _ _ _

end
end PerfectCompleteness.RecursiveSampler

end OAI
