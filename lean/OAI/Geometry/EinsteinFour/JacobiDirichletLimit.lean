import OAI.Geometry.EinsteinFour.JacobiSchemeMatrix
import OAI.Geometry.EinsteinFour.JacobiApproximation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Instances.Matrix

namespace OAI

/-! The Dirichlet determinant converges to the actual Jacobi determinant. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

theorem curvatureDirichlet_det_tendsto_of_position_tendsto {t : ℝ} (ht : t ≠ 0)
    (R : ℕ → ℕ → NormalMatrix) (hR : ∀ N i, (R N i)ᵀ = R N i)
    (J : NormalMatrix)
    (hunit : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 1 ≤ i → i ≤ N + 1 →
      IsUnit (normalizedDiscrete (R N) (t / (N + 1)) i).det)
    (hX : Tendsto (fun N : ℕ => discretePosition (R N) (t / (N + 1)) (N + 1))
      atTop (nhds J)) :
    Tendsto (fun N : ℕ => (t / (N + 1)) ^ 3 *
      (curvatureDirichlet t (fun i : Fin N => R N (i.val + 1) - 1)).det)
      atTop (nhds J.det) := by
  have hc : Continuous (fun A : NormalMatrix => A.det) := continuous_id.matrix_det
  apply ((hc.tendsto J).comp hX).congr'
  filter_upwards [hunit] with N hu
  dsimp only [Function.comp_apply]
  rw [curvatureDirichlet_determinant ht (R N) (hR N) hu]
  have hh : t / (N + 1 : ℝ) ≠ 0 := div_ne_zero ht (by positivity)
  have hid : (t / (N + 1)) • normalizedDiscrete (R N) (t / (N + 1)) (N + 1) =
      discretePosition (R N) (t / (N + 1)) (N + 1) := by
    simp only [normalizedDiscrete, smul_smul, mul_inv_cancel₀ hh, one_smul]
  rw [← hid, Matrix.det_smul, Fintype.card_fin]


theorem curvatureDirichlet_det_tendsto_of_error {t C : ℝ} (ht : t ≠ 0)
    (R : ℕ → ℕ → NormalMatrix) (hR : ∀ N i, (R N i)ᵀ = R N i)
    (J : NormalMatrix)
    (hunit : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 1 ≤ i → i ≤ N + 1 →
      IsUnit (normalizedDiscrete (R N) (t / (N + 1)) i).det)
    (herr : ∀ᶠ N : ℕ in atTop,
      ‖discretePosition (R N) (t / (N + 1)) (N + 1) - J‖ ≤ C / (N + 1)) :
    Tendsto (fun N : ℕ => (t / (N + 1)) ^ 3 *
      (curvatureDirichlet t (fun i : Fin N => R N (i.val + 1) - 1)).det)
      atTop (nhds J.det) := by
  have hzero : Tendsto (fun N : ℕ => C / (N + 1)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
  have hnorm : Tendsto (fun N : ℕ =>
      ‖discretePosition (R N) (t / (N + 1)) (N + 1) - J‖) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) herr hzero
  exact curvatureDirichlet_det_tendsto_of_position_tendsto ht R hR J hunit
    (tendsto_iff_norm_sub_tendsto_zero.mpr hnorm)

end

end PositiveEinsteinFour.Jacobi

end OAI
