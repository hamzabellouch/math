import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Laughlin
open scoped BigOperators InnerProductSpace

theorem quadratic_perturbation_bound {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (R : ι → ι → ℝ) (x : ι → F) (ε : ℝ) (hε : 0 ≤ ε)
    (hR : ∀ i j, |R i j| ≤ ε) :
    |∑ i, ∑ j, R i j * ⟪x i, x j⟫_ℝ| ≤
      ε * (Fintype.card ι : ℝ) * ∑ i, ‖x i‖^2 := by
  have hp (i j : ι) :
      |R i j * ⟪x i, x j⟫_ℝ| ≤ ε * (‖x i‖^2 + ‖x j‖^2) / 2 := by
    rw [abs_mul]
    have hi : |⟪x i, x j⟫_ℝ| ≤ (‖x i‖^2 + ‖x j‖^2)/2 := by
      have hc := abs_real_inner_le_norm (x i) (x j)
      nlinarith [sq_nonneg (‖x i‖ - ‖x j‖)]
    calc
      |R i j| * |⟪x i, x j⟫_ℝ| ≤ ε * ((‖x i‖^2 + ‖x j‖^2)/2) :=
        mul_le_mul (hR i j) hi (abs_nonneg _) hε
      _ = _ := by ring
  calc
    |∑ i, ∑ j, R i j * ⟪x i, x j⟫_ℝ| ≤
        ∑ i, ∑ j, |R i j * ⟪x i, x j⟫_ℝ| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : ι, ∑ j : ι, ε * (‖x i‖^2 + ‖x j‖^2) / 2 := by
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = _ := by
      simp only [mul_add, add_div, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring_nf
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem relative_lower_bound (base error energy δ : ℝ)
    (hbase : 0 ≤ base) (herr : |error| ≤ δ * energy) :
    -(δ * energy) ≤ base + error := by
  have := (abs_le.mp herr).1
  linarith

end Laughlin

end OAI
