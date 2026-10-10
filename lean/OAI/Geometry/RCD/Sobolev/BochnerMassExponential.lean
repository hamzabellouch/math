import OAI.Geometry.RCD.Sobolev.RadialCutoffNorm
import OAI.Geometry.RCD.Metric.GlobalVolumeGrowth

namespace OAI

/-! # Exponential envelopes for the quantitative local Bochner masses -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] (μ : Measure X)

theorem radial_mass_bound_le_exp (p : X) {M V B R : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hvol : μ.real (closedBall p (2*R)) ≤ V*Real.exp (B*R))
    {s : ℝ} (hs : s ≤ M*Real.sqrt ((1+R⁻¹^2)*μ.real (closedBall p (2*R)))) :
    s ≤ M*(1+2*V)*Real.exp (B*R) := by
  have hR0 : 0 < R := by linarith
  have hinv : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hinv2 : R⁻¹^2 ≤ 1 := by nlinarith [inv_nonneg.mpr hR0.le]
  have he : 1 ≤ Real.exp (B*R) := Real.one_le_exp (mul_nonneg hB hR0.le)
  have hbase : (1+R⁻¹^2)*μ.real (closedBall p (2*R)) ≤ 2*V*Real.exp (B*R) := by
    calc
      _ ≤ 2*μ.real (closedBall p (2*R)) :=
        mul_le_mul_of_nonneg_right (by linarith) measureReal_nonneg
      _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hvol (by norm_num : (0:ℝ) ≤ 2)]
  have hsqrt : Real.sqrt ((1+R⁻¹^2)*μ.real (closedBall p (2*R))) ≤
      (1+2*V)*Real.exp (B*R) := by
    have hp : 0 ≤ (1+R⁻¹^2)*μ.real (closedBall p (2*R)) := by positivity
    have ht := Real.sq_sqrt hp
    have hs := Real.sqrt_nonneg ((1+R⁻¹^2)*μ.real (closedBall p (2*R)))
    have hlin : Real.sqrt ((1+R⁻¹^2)*μ.real (closedBall p (2*R))) ≤
        1+(1+R⁻¹^2)*μ.real (closedBall p (2*R)) := by
      nlinarith [sq_nonneg (Real.sqrt ((1+R⁻¹^2)*μ.real (closedBall p (2*R)))-1)]
    nlinarith only [hlin,hbase,he]
  exact hs.trans ((mul_le_mul_of_nonneg_left hsqrt hM).trans_eq (by ring))

end RegularPointCoordinates

end

end OAI
