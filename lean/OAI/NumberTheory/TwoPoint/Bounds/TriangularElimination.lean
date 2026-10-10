import OAI.NumberTheory.TwoPoint.Bounds.MixedDifference
import Mathlib.Logic.Equiv.Prod

namespace OAI

/-! Successive elimination for finite product laws and triangular events. -/

namespace TwoPointCorrelations

open Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

def restoreCoordinate (i : ι) (a : A) (y : {j : ι // j ≠ i} → A) (j : ι) : A :=
  if h : j = i then a else y ⟨j, h⟩

omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_same (i : ι) (a : A) (y : {j : ι // j ≠ i} → A) :
    restoreCoordinate i a y i = a := by simp [restoreCoordinate]

omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_other (i : ι) (a : A) (y : {j : ι // j ≠ i} → A)
    (j : {j : ι // j ≠ i}) : restoreCoordinate i a y j = y j := by
  simp [restoreCoordinate, j.property]

omit [Fintype ι] [Fintype A] in
lemma restoreCoordinate_update (i : ι) (a b : A) (y : {j : ι // j ≠ i} → A) :
    Function.update (restoreCoordinate i a y) i b = restoreCoordinate i b y := by
  funext j
  by_cases hj : j = i <;> simp [restoreCoordinate, hj]

namespace FiniteLaw

lemma independent_weight_restore (μ : ι → FiniteLaw A) (i : ι)
    (a : A) (y : {j : ι // j ≠ i} → A) :
    (independent μ).weight (restoreCoordinate i a y) =
      (μ i).weight a * (independent (fun j : {j : ι // j ≠ i} => μ j)).weight y := by
  change (∏ j, (μ j).weight (restoreCoordinate i a y j)) = _
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ i)]
  rw [restoreCoordinate_same]
  congr 1
  rw [Finset.prod_subtype (p := fun j : ι => j ≠ i) (univ \ {i}) (by intro j; simp)]
  apply prod_congr rfl
  intro j _
  rw [restoreCoordinate_other]

/-- Expose one original independent coordinate, keeping all other variables
fixed and retaining their original product law. -/
lemma independent_average_one_coordinate (μ : ι → FiniteLaw A) (i : ι)
    (F : (ι → A) → ℝ) :
    (independent μ).average F =
      (independent (fun j : {j : ι // j ≠ i} => μ j)).average (fun y =>
        (μ i).average (fun a => F (restoreCoordinate i a y))) := by
  let e := Equiv.funSplitAt i A
  have he (a : A) (y : {j : ι // j ≠ i} → A) : e.symm (a, y) = restoreCoordinate i a y := by
    funext j
    by_cases hj : j = i <;> simp [e, Equiv.funSplitAt, Equiv.piSplitAt, restoreCoordinate, hj]
  calc
    _ = ∑ z : A × ({j : ι // j ≠ i} → A),
        (independent μ).weight (restoreCoordinate i z.1 z.2) * F (restoreCoordinate i z.1 z.2) := by
      simpa only [he, average] using (e.symm.sum_comp (fun x => (independent μ).weight x * F x)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [independent_weight_restore, average, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro a _
      ring

/-- One elimination step. All retained events ignore the variable being
summed; only its own event is charged its conditional probability bound. -/
theorem eliminate_coordinate [Nonempty A] (μ : ι → FiniteLaw A) (i : ι)
    (E F : (ι → A) → Prop) (δ : ℝ)
    (hE : ∀ x a, E (Function.update x i a) ↔ E x)
    (hF : ∀ x, (μ i).probability (fun a => F (Function.update x i a)) ≤ δ) :
    (independent μ).probability (fun x => E x ∧ F x) ≤
      δ * (independent μ).probability E := by
  classical
  let a₀ : A := Classical.choice inferInstance
  let ν := independent (fun j : {j : ι // j ≠ i} => μ j)
  have hE' (y : {j : ι // j ≠ i} → A) (a : A) :
      E (restoreCoordinate i a y) ↔ E (restoreCoordinate i a₀ y) := by
    simpa only [restoreCoordinate_update] using hE (restoreCoordinate i a₀ y) a
  have hF' (y : {j : ι // j ≠ i} → A) :
      (μ i).probability (fun a => F (restoreCoordinate i a y)) ≤ δ := by
    simpa only [restoreCoordinate_update] using hF (restoreCoordinate i a₀ y)
  have hrest : (independent μ).probability E =
      ν.average (fun y => if E (restoreCoordinate i a₀ y) then 1 else 0) := by
    rw [probability, independent_average_one_coordinate μ i]
    apply congrArg ν.average
    funext y
    simp only [hE']
    exact (μ i).average_const _
  rw [hrest, ← average_const_mul]
  unfold probability
  rw [independent_average_one_coordinate μ i]
  apply ν.average_mono
  intro y
  by_cases hy : E (restoreCoordinate i a₀ y)
  · simpa only [probability, hE', hy, true_and, ite_true, mul_one] using hF' y
  · simp only [hE', hy, false_and, ite_false, average_const, mul_zero]
    exact le_rfl

/-- Simultaneous triangular events cost one conditional factor per selected
coordinate. The retained earlier events explicitly ignore every later
coordinate, including any appearance as a controlling modulus. -/
theorem triangular_probability_bound [LinearOrder ι] [Nonempty A]
    (μ : ι → FiniteLaw A) (E : ι → (ι → A) → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (R : Finset ι)
    (hdepends : ∀ i ∈ R, ∀ j ∈ R, i < j → ∀ x a,
      E i (Function.update x j a) ↔ E i x)
    (hconditional : ∀ i ∈ R, ∀ x,
      (μ i).probability (fun a => E i (Function.update x i a)) ≤ δ) :
    (independent μ).probability (fun x => ∀ i ∈ R, E i x) ≤ δ ^ R.card := by
  classical
  revert hdepends hconditional
  induction R using Finset.strongInductionOn with
  | _ R ih =>
    intro hdepends hconditional
    by_cases hR : R.Nonempty
    · let i := R.max' hR
      have hi : i ∈ R := max'_mem R hR
      have hjlt (j : ι) (hj : j ∈ R.erase i) : j < i := by
        have hjR := (mem_erase.mp hj).2
        have hji := (mem_erase.mp hj).1
        exact lt_of_le_of_ne (le_max' R j hjR) hji
      have hretained : ∀ x a,
          (∀ j ∈ R.erase i, E j (Function.update x i a)) ↔ ∀ j ∈ R.erase i, E j x := by
        intro x a
        constructor <;> intro hx j hj
        · exact (hdepends j (mem_erase.mp hj).2 i hi (hjlt j hj) x a).mp (hx j hj)
        · exact (hdepends j (mem_erase.mp hj).2 i hi (hjlt j hj) x a).mpr (hx j hj)
      have hstep := eliminate_coordinate μ i (fun x => ∀ j ∈ R.erase i, E j x)
        (E i) δ hretained (hconditional i hi)
      have hevent : (fun x => ∀ j ∈ R, E j x) =
          (fun x => (∀ j ∈ R.erase i, E j x) ∧ E i x) := by
        funext x
        apply propext
        constructor
        · intro hx
          exact ⟨fun j hj => hx j (mem_erase.mp hj).2, hx i hi⟩
        · rintro ⟨hx, hxi⟩ j hj
          by_cases hji : j = i
          · simpa only [hji] using hxi
          · exact hx j (mem_erase.mpr ⟨hji, hj⟩)
      rw [hevent]
      apply hstep.trans
      have hrest := ih (R.erase i) (Finset.erase_ssubset hi)
        (fun j hj k hk hjk x a => hdepends j (mem_erase.mp hj).2 k (mem_erase.mp hk).2 hjk x a)
        (fun j hj => hconditional j (mem_erase.mp hj).2)
      have hmul := mul_le_mul_of_nonneg_left hrest hδ
      have hcard : R.card = (R.erase i).card + 1 := by
        rw [card_erase_of_mem hi]
        have hpos := card_pos.mpr hR
        omega
      simpa only [hcard, pow_succ, mul_comm] using hmul
    · have hzero : R = ∅ := not_nonempty_iff_eq_empty.mp hR
      rw [hzero, card_empty, pow_zero]
      exact probability_le_one _ _

end FiniteLaw

end TwoPointCorrelations

end OAI
