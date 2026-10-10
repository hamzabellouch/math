import OAI.Geometry.EinsteinFour.JacobiODELimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! The reference determinant limit is instantiated by the sine Jacobi curve. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

def sineJacobi (t : ℝ) : RegularJacobi t where
  R := fun _ => 1
  J := fun s => Real.sin s • 1
  V := fun s => Real.cos s • 1
  K := 1
  Lx := 1
  Lv := 1
  F := 1
  K_nonneg := zero_le_one
  Lx_nonneg := zero_le_one
  Lv_nonneg := zero_le_one
  F_nonneg := zero_le_one
  initial_position := by simp
  initial_velocity := by simp
  symmetric := by intro s; simp
  curvature_bound := by intro s hs; simp
  position_derivative := by
    intro s hs
    exact (Real.hasDerivAt_sin s).smul_const (1 : NormalMatrix)
  velocity_derivative := by
    intro s hs
    simpa only [one_mul, neg_smul] using
      (Real.hasDerivAt_cos s).smul_const (1 : NormalMatrix)
  velocity_lipschitz := by
    intro s hs r hr
    simpa only [← sub_smul, norm_smul, norm_one, mul_one, one_mul, Real.norm_eq_abs]
      using Real.abs_cos_sub_cos_le s r
  acceleration_lipschitz := by
    intro s hs r hr
    calc
      ‖-((1 : NormalMatrix) * (Real.sin s • 1)) - -(1 * (Real.sin r • 1))‖ =
          ‖(Real.sin s - Real.sin r) • (1 : NormalMatrix)‖ := by
            rw [one_mul, one_mul, neg_sub_neg, norm_sub_rev, sub_smul]
      _ ≤ 1 * |s - r| := by
        simpa only [norm_smul, norm_one, mul_one, one_mul, Real.norm_eq_abs] using
          Real.abs_sin_sub_sin_le s r
  force_bound := by
    intro s hs
    simpa only [one_mul, norm_smul, norm_one, mul_one, Real.norm_eq_abs] using
      Real.abs_sin_le_one s

theorem sineJacobi_preconjugate {t : ℝ} (htπ : t < Real.pi) :
    ∀ s, 0 < s → s ≤ t → IsUnit ((sineJacobi t).J s) := by
  intro s hs hst
  have hu : IsUnit (Real.sin s) :=
    isUnit_iff_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hs (hst.trans_lt htπ)).ne'
  simpa only [sineJacobi, Algebra.algebraMap_eq_smul_one] using
    hu.map (algebraMap ℝ NormalMatrix)

theorem reference_determinant_tendsto {t : ℝ} (ht : 0 < t) (htπ : t < Real.pi) :
    Tendsto (fun N : ℕ => (t / (N + 1)) ^ 3 * (referenceMatrix t N).det ^ 3)
      atTop (nhds (Real.sin t ^ 3)) := by
  have h := (sineJacobi t).curvatureDirichlet_det_tendsto ht
    (sineJacobi_preconjugate htπ)
  have hz (N : ℕ) : Matrix.blockDiagonal (fun _ : Fin N => (0 : NormalMatrix)) = 0 :=
    Matrix.blockDiagonal_zero
  simpa only [sineJacobi, meshStep, curvatureDirichlet, sub_self,
    hz, smul_zero, sub_zero, det_scalarLift,
    Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] using h

end

end PositiveEinsteinFour.Jacobi

end OAI
