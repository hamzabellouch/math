import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section

open scoped BigOperators

namespace Problem336AdditiveD139

theorem sum_abs_row_eq {F : Type u_1} [Fintype F] (c : F → ℝ) (i : F)
    (hdiag : 0 ≤ c i) (hoff : ∀ j, j ≠ i → c j ≤ 0) :
    (∑ j : F, |c j|) = 2 * c i - ∑ j : F, c j := by
  classical
  have hsum := Finset.sum_erase_add Finset.univ c (Finset.mem_univ i)
  have habs := Finset.sum_erase_add Finset.univ (fun j => |c j|) (Finset.mem_univ i)
  have hrest : (∑ j ∈ Finset.univ.erase i, |c j|) =
      -(∑ j ∈ Finset.univ.erase i, c j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact abs_of_nonpos (hoff j (Finset.mem_erase.mp hj).1)
  rw [hrest, abs_of_nonneg hdiag] at habs
  linarith

theorem sum_abs_row_le_twice_diag {F : Type u_2} [Fintype F] (c : F → ℝ) (i : F)
    (hdiag : 0 ≤ c i) (hoff : ∀ j, j ≠ i → c j ≤ 0)
    (hrow : 0 ≤ ∑ j : F, c j) :
    (∑ j : F, |c j|) ≤ 2 * c i := by
  rw [sum_abs_row_eq c i hdiag hoff]
  linarith

theorem row_sum_nonneg_of_dummy {F : Type u_3} {D : Type u_4} [Fintype F] [Fintype D]
    (c : F → ℝ) (d : D → ℝ)
    (hzero : (∑ j : F, c j) + (∑ j : D, d j) = 0)
    (hdummy : ∀ j, d j ≤ 0) : 0 ≤ ∑ j : F, c j := by
  have hle : (∑ j : D, d j) ≤ 0 := Finset.sum_nonpos (fun j _ => hdummy j)
  linarith

end Problem336AdditiveD139

end

end OAI
