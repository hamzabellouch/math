import Mathlib

namespace OAI

universe u

noncomputable section
open scoped BigOperators
namespace Problem313

variable {ι : Type u} [DecidableEq ι]

/-- Reinsert one Boolean coordinate in a function on the remaining coordinates. -/
def russoInsert (i : ι) (b : Bool) (z : {j : ι // j ≠ i} → Bool) : ι → Bool :=
  (Equiv.funSplitAt i Bool).symm (b, z)

@[simp] theorem russoInsert_self (i : ι) (b : Bool)
    (z : {j : ι // j ≠ i} → Bool) : russoInsert i b z i = b := by
  simp [russoInsert, Equiv.funSplitAt_symm_apply]

@[simp] theorem russoInsert_of_ne (i : ι) (b : Bool)
    (z : {j : ι // j ≠ i} → Bool) (j : ι) (h : j ≠ i) :
    russoInsert i b z j = z ⟨j,h⟩ := by
  simp [russoInsert, Equiv.funSplitAt_symm_apply, h]

@[simp] theorem update_russoInsert (i : ι) (b c : Bool)
    (z : {j : ι // j ≠ i} → Bool) :
    Function.update (russoInsert i b z) i c = russoInsert i c z := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

variable [Fintype ι]

/-- Splitting a finite Boolean cube at one coordinate. -/
theorem sum_bool_split (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x, g x) = ∑ z : {j : ι // j ≠ i} → Bool,
      (g (russoInsert i true z) + g (russoInsert i false z)) := by
  rw [← (Equiv.funSplitAt i Bool).symm.sum_comp g]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  rfl

/-- The product excluding a coordinate does not depend on that coordinate. -/
theorem prod_erase_russoInsert (p : ℝ) (i : ι) (b c : Bool)
    (z : {j : ι // j ≠ i} → Bool) :
    (∏ j ∈ Finset.univ.erase i, if russoInsert i b z j = true then p else 1-p) =
    ∏ j ∈ Finset.univ.erase i, if russoInsert i c z j = true then p else 1-p := by
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [hji]

/-- A Bernoulli weight factors at a chosen coordinate. -/
theorem prod_russoInsert (p : ℝ) (i : ι) (b : Bool)
    (z : {j : ι // j ≠ i} → Bool) :
    (∏ j, if russoInsert i b z j = true then p else 1-p) =
    (if b = true then p else 1-p) *
      ∏ j ∈ Finset.univ.erase i, if russoInsert i false z j = true then p else 1-p := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => if russoInsert i b z j = true then p else 1-p) (Finset.mem_univ i)]
  rw [prod_erase_russoInsert p i b false]
  simp

/-- Finite reindexing identity behind the Russo--Margulis derivative formula.
No positivity assumptions on the bias or the observable are needed. -/
theorem russo_sum_reindex (p : ℝ) (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x : ι → Bool, (if x i = true then (1 : ℝ) else -1) *
      (∏ j ∈ Finset.univ.erase i, if x j = true then p else 1-p) * g x) =
    ∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) *
      (g (Function.update x i true) - g (Function.update x i false)) := by
  rw [sum_bool_split i, sum_bool_split i]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [russoInsert_self, Bool.false_eq_true,
    ↓reduceIte, update_russoInsert, prod_russoInsert]
  rw [prod_erase_russoInsert p i true false]
  ring

/-- Integrating out one coordinate is unchanged by Bernoulli resampling. -/
theorem sum_weight_conditioning (p : ℝ) (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) * g x) =
    ∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) *
      ((1-p) * g (Function.update x i false) + p * g (Function.update x i true)) := by
  rw [sum_bool_split i, sum_bool_split i]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [update_russoInsert, prod_russoInsert, Bool.false_eq_true, ↓reduceIte]
  ring

/-- A reset observable can be integrated on the cube with that coordinate removed. -/
theorem sum_weight_update (p : ℝ) (i : ι) (b : Bool) (g : (ι → Bool) → ℝ) :
    (∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) *
      g (Function.update x i b)) =
    ∑ z : {j : ι // j ≠ i} → Bool,
      (∏ j ∈ Finset.univ.erase i, if russoInsert i false z j = true then p else 1-p) *
      g (russoInsert i b z) := by
  rw [sum_bool_split i]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [update_russoInsert, prod_russoInsert, Bool.false_eq_true, ↓reduceIte]
  ring

/-- Discrete integration by parts for a centered Bernoulli coordinate. -/
theorem sum_weight_centered_coordinate (p : ℝ) (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) * g x *
      ((if x i = true then (1 : ℝ) else 0) - p)) =
    p * (1-p) * ∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) *
      (g (Function.update x i true) - g (Function.update x i false)) := by
  rw [sum_bool_split i, sum_bool_split i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [russoInsert_self, update_russoInsert, prod_russoInsert,
    Bool.false_eq_true, ↓reduceIte]
  ring

end Problem313

end

end OAI
