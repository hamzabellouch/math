import OAI.Geometry.EinsteinFour.JacobiRadialODE
import OAI.Geometry.EinsteinFour.JacobiMatrixLoss
import OAI.Geometry.EinsteinFour.JacobiAverage

namespace OAI

/-! The quantitative radial deficit before the first conjugate point. -/

namespace PositiveEinsteinFour.Jacobi.RegularJacobi

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

variable {t : ℝ} (d : RegularJacobi t)

/-- The actual Jacobi determinant loses a definite fraction of the squared
sine-weighted averaged curvature. -/
theorem radial_determinant_deficit (ht : 0 < t) (htπ : t < Real.pi)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s))
    (hR : Continuous d.R) (hRpos : ∀ s, (d.R s).PosSemidef)
    (htrace : ∀ s, (d.R s).trace = 3)
    {L : ℝ} (hL : 0 ≤ L)
    (hc : Continuous (fun s => Averages.sineWeight s • radialCurvature d.R t s))
    (hLip : ∀ s r,
      ‖Averages.sineWeight s • radialCurvature d.R t s -
        Averages.sineWeight r • radialCurvature d.R t r‖ ≤ L * |s - r|) :
    (d.J t).det ≤ Real.sin t ^ 3 *
      (1 - lossFactor (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) / 6 *
        ‖∫ s in (0 : ℝ)..1, Averages.sineWeight s • radialCurvature d.R t s‖ ^ 2) := by
  let A := radialCurvature d.R t
  let B : NormalMatrix := ∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s
  have hA : Continuous A := (hR.comp (continuous_id.mul_const t)).sub continuous_const
  have hAt : ∀ s, (A s).trace = 0 := fun s => by
    simp [A, radialCurvature, Matrix.trace_sub, htrace]
  have hAp : ∀ s, (A s + 1).PosSemidef := fun s => by
    simpa only [A, radialCurvature, sub_add_cancel] using hRpos (s * t)
  have hBt : B.trace = 0 := sine_average_trace hA hAt
  have hBp : (B + 1).PosSemidef := sine_average_add_one_posSemidef hA hAp
  have hBh : B.IsHermitian := by
    simpa only [add_sub_cancel_right] using hBp.isHermitian.sub (isHermitian_one :
      (1 : NormalMatrix).IsHermitian)
  have hβ : 0 ≤ t ^ 2 / (Real.pi ^ 2 - t ^ 2) := by
    apply div_nonneg (sq_nonneg t)
    nlinarith [Real.pi_pos]
  have hdef := matrix_preconjugate_loss hBh hβ hBt hBp
    (d.radial_compression_posSemidef ht htπ hpre hL hc hLip)
  exact (d.radial_determinant_comparison ht htπ hpre htrace hL hc hLip).trans
    (mul_le_mul_of_nonneg_left hdef (pow_nonneg (Real.sin_pos_of_pos_of_lt_pi ht htπ).le 3))

/-- After conjugacy the truncated radial density is zero. The same upper
bound stays nonnegative from the curvature range alone. -/
theorem radial_deficit_nonneg (ht : 0 ≤ t) (htπ : t < Real.pi)
    (hR : Continuous d.R) (hRpos : ∀ s, (d.R s).PosSemidef)
    (htrace : ∀ s, (d.R s).trace = 3) :
    0 ≤ Real.sin t ^ 3 *
      (1 - lossFactor (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) / 6 *
        ‖∫ s in (0 : ℝ)..1, Averages.sineWeight s • radialCurvature d.R t s‖ ^ 2) := by
  let A := radialCurvature d.R t
  let B : NormalMatrix := ∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s
  have hA : Continuous A := (hR.comp (continuous_id.mul_const t)).sub continuous_const
  have hAt : ∀ s, (A s).trace = 0 := fun s => by
    simp [A, radialCurvature, Matrix.trace_sub, htrace]
  have hAp : ∀ s, (A s + 1).PosSemidef := fun s => by
    simpa only [A, radialCurvature, sub_add_cancel] using hRpos (s * t)
  have hBt : B.trace = 0 := sine_average_trace hA hAt
  have hBp : (B + 1).PosSemidef := sine_average_add_one_posSemidef hA hAp
  have hBh : B.IsHermitian := by
    simpa only [add_sub_cancel_right] using hBp.isHermitian.sub (isHermitian_one :
      (1 : NormalMatrix).IsHermitian)
  have hl := matrix_postconjugate_loss hBh
    (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) hBt hBp
  exact mul_nonneg (pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht htπ.le) 3)
    (sub_nonneg.mpr hl)

end

end PositiveEinsteinFour.Jacobi.RegularJacobi

end OAI
