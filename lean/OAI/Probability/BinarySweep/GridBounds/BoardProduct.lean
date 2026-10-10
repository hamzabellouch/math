import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Density

theorem product_on_board_le_exp {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) (C : ℝ)
    (hs : ∑ i, x i ≤ C) :
    ∏ i ∈ S, x i ≤ Real.exp (C - S.card) := by
  have he (a : ℝ) : a ≤ Real.exp (a-1) := by
    have := Real.add_one_le_exp (a-1)
    linarith
  calc
    _ ≤ ∏ i ∈ S, Real.exp (x i - 1) :=
      Finset.prod_le_prod₀ (fun index _ => hx index) (fun index _ => he (x index))
    _ = Real.exp ((∑ i ∈ S, x i) - S.card) := by
      rw [← Real.exp_sum,Finset.sum_sub_distrib]
      simp
    _ ≤ Real.exp (C - S.card) := by
      apply Real.exp_le_exp.mpr
      exact sub_le_sub_right ((Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ S) (fun i _ _ => hx i)).trans hs) _

 theorem rectangular_product_holes {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (S : Finset (I × J)) (x : I → J → ℝ)
    (hx : ∀ i j, 0 ≤ x i j)
    (hs : ∀ j, ∑ i, x i j ≤ Fintype.card I) :
    ∏ t ∈ S, x t.1 t.2 ≤
      Real.exp (Fintype.card I * Fintype.card J - S.card) := by
  apply product_on_board_le_exp S (fun t => x t.1 t.2) (fun t => hx t.1 t.2)
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simpa [mul_comm] using Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hs j)

end BinaryCoordinateSweeps.Density

end

end OAI
