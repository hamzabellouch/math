import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace OAI

/-!
# Indexed Subset Sum and the random sign transformation

The input is indexed: equal numerical values at different indices remain
different choices. The empty subset is included. These definitions and lemmas
implement the sign transformation in §3 of *A Low-Space Algorithm for Worst-Case
Subset Sum* (equation `alg:sign-flip`). No distributional assumption on the
input weights is made.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators symmDiff

/-- A positive-integer input, with a nonnegative target. -/
structure Instance (n : ℕ) where
  values : Fin n → ℕ
  positive : ∀ i, 0 < values i
  target : ℕ

/-- Exact integer weight of an indexed subset. -/
def weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (S : Finset ι) : ℤ :=
  ∑ i, if i ∈ S then a i else 0

/-- The decision predicate includes the empty subset. -/
def Solvable {n : ℕ} (I : Instance n) : Prop :=
  ∃ S : Finset (Fin n), weight (fun i => (I.values i : ℤ)) S = I.target

@[simp] theorem weight_empty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) : weight a ∅ = 0 := by
  simp [weight]

theorem zero_target_solvable {n : ℕ} (I : Instance n) (h : I.target = 0) :
    Solvable I := by
  exact ⟨∅, by simp [h]⟩

/-- Negate precisely the indices in `F`. -/
def flip {ι : Type*} [DecidableEq ι] (a : ι → ℤ) (F : Finset ι) (i : ι) : ℤ :=
  if i ∈ F then -a i else a i

/-- The signed weight is a translated original weight after toggling indices. -/
theorem weight_flip {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (F S : Finset ι) :
    weight (flip a F) S = weight a (S ∆ F) - weight a F := by
  simp only [weight]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hS : i ∈ S <;> by_cases hF : i ∈ F <;>
    simp [flip, Finset.mem_symmDiff, hS, hF]

/-- Toggling the sign set translates solutions in both directions. -/
theorem signed_solution_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (t : ℤ) (F S : Finset ι) :
    weight (flip a F) S = t - weight a F ↔ weight a (S ∆ F) = t := by
  rw [weight_flip]
  omega

theorem signed_solvable_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (t : ℤ) (F : Finset ι) :
    (∃ S, weight (flip a F) S = t - weight a F) ↔ ∃ S, weight a S = t := by
  constructor
  · rintro ⟨S, h⟩
    exact ⟨S ∆ F, (signed_solution_iff a t F S).mp h⟩
  · rintro ⟨S, h⟩
    refine ⟨S ∆ F, (signed_solution_iff a t F (S ∆ F)).mpr ?_⟩
    simpa only [symmDiff_assoc, symmDiff_self, symmDiff_bot] using h

/-- Disjoint joins preserve exact weights. -/
theorem weight_union {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) {S T : Finset ι} (h : Disjoint S T) :
    weight a (S ∪ T) = weight a S + weight a T := by
  simp only [weight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi : ¬ (i ∈ S ∧ i ∈ T) := by
    intro hi
    exact Finset.disjoint_left.mp h hi.1 hi.2
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

/-- An exact disjoint signed match certifies an original indexed solution. -/
theorem match_sound {n : ℕ} (I : Instance n) (F L R : Finset (Fin n))
    (hd : Disjoint L R)
    (hm : weight (flip (fun i => (I.values i : ℤ)) F) L +
      weight (flip (fun i => (I.values i : ℤ)) F) R =
      (I.target : ℤ) - weight (fun i => (I.values i : ℤ)) F) :
    Solvable I := by
  refine ⟨(L ∪ R) ∆ F, ?_⟩
  apply (signed_solution_iff _ _ F (L ∪ R)).mp
  rw [weight_union _ hd]
  exact hm

/-- A dictionary key retains the exact weight and the entire top-block mask. -/
structure Entry (ι : Type*) where
  value : ℤ
  mask : Finset ι

/-- A retained entry has a subset witness within its parent's allowed domain. -/
def Represents {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (domain top : Finset ι) (e : Entry ι) : Prop :=
  ∃ S ⊆ domain, weight a S = e.value ∧ S ∩ top = e.mask

/-- If the parents share only top indices, their masks decide compatibility. -/
theorem disjoint_of_top_masks {ι : Type*} [DecidableEq ι]
    {leftDomain rightDomain top L R : Finset ι}
    (hshared : leftDomain ∩ rightDomain ⊆ top)
    (hL : L ⊆ leftDomain) (hR : R ⊆ rightDomain)
    (hmasks : Disjoint (L ∩ top) (R ∩ top)) : Disjoint L R := by
  apply Finset.disjoint_left.mpr
  intro i hiL hiR
  have hit : i ∈ top := hshared (Finset.mem_inter.mpr ⟨hL hiL, hR hiR⟩)
  exact Finset.disjoint_left.mp hmasks
    (Finset.mem_inter.mpr ⟨hiL, hit⟩) (Finset.mem_inter.mpr ⟨hiR, hit⟩)

/-- Soundness depends only on the stored key, so duplicate witnesses can be
discarded without changing the existence of a compatible exact match. -/
theorem entry_match_sound {n : ℕ} (I : Instance n) (F : Finset (Fin n))
    {leftDomain rightDomain top : Finset (Fin n)}
    (hshared : leftDomain ∩ rightDomain ⊆ top) {l r : Entry (Fin n)}
    (hl : Represents (flip (fun i => (I.values i : ℤ)) F) leftDomain top l)
    (hr : Represents (flip (fun i => (I.values i : ℤ)) F) rightDomain top r)
    (hd : Disjoint l.mask r.mask)
    (hw : l.value + r.value = I.target - weight (fun i => (I.values i : ℤ)) F) :
    Solvable I := by
  obtain ⟨L, hL, hwL, hmL⟩ := hl
  obtain ⟨R, hR, hwR, hmR⟩ := hr
  apply match_sound I F L R
  · apply disjoint_of_top_masks hshared hL hR
    rwa [hmL, hmR]
  · rwa [hwL, hwR]

end LowSpaceSubsetSum

end OAI
