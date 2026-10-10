import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialEnergyZero
import Mathlib.Topology.Order.OrderClosed

namespace OAI

/-! Positivity and monotonicity turn vanishing outer traces into zero energy. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialScalarForm_mono (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (q f : ℝ → ℝ) (hq : Continuous q)
    (hqn : ∀ r, 0 ≤ r → 0 ≤ q r) (hf : ContDiff ℝ 1 f) :
    MonotoneOn (fun R => radialScalarForm n z R q f f) (Ici 0) := by
  have hG := (radialMassDensity_continuous n z hX hz).mul
    (hf.continuous_deriv_one.pow 2)
  have hP := ((radialMassDensity_continuous n z hX hz).mul hq).mul (hf.continuous.pow 2)
  intro R hR S _hS hRS
  have hGn : 0 ≤ ∫ r in R..S, radialMassDensity n z r*(deriv f r)^2 := by
    apply intervalIntegral.integral_nonneg hRS
    intro r hr
    have hr0 := hR.trans hr.1
    unfold radialMassDensity
    positivity
  have hPn : 0 ≤ ∫ r in R..S, radialMassDensity n z r*q r*(f r)^2 := by
    apply intervalIntegral.integral_nonneg hRS
    intro r hr
    have hr0 := hR.trans hr.1
    have hqr := hqn r hr0
    unfold radialMassDensity
    positivity
  have hGa := intervalIntegral.integral_add_adjacent_intervals
    (hG.intervalIntegrable (μ := MeasureTheory.volume) 0 R)
    (hG.intervalIntegrable (μ := MeasureTheory.volume) R S)
  have hPa := intervalIntegral.integral_add_adjacent_intervals
    (hP.intervalIntegrable (μ := MeasureTheory.volume) 0 R)
    (hP.intervalIntegrable (μ := MeasureTheory.volume) R S)
  simp only [Pi.mul_apply,Pi.pow_apply] at hGa hPa
  change radialScalarForm n z R q f f ≤ radialScalarForm n z S q f f
  rw [radialScalarForm_diag,radialScalarForm_diag]
  linarith

theorem nonnegative_monotone_zero_of_vanishing_bound (E B : ℝ → ℝ) (c : ℝ)
    (hc : 0 < c) (hEn : ∀ R, 0 ≤ R → 0 ≤ E R)
    (hEm : MonotoneOn E (Ici 0)) (hB : Tendsto B atTop (nhds 0))
    (hbound : ∀ᶠ R in atTop, c*E R ≤ B R) :
    ∀ R, 0 ≤ R → E R=0 := by
  intro R hR
  have hle : c*E R ≤ 0 := by
    apply ge_of_tendsto hB
    filter_upwards [hbound,eventually_ge_atTop R] with S hS hRS
    exact (mul_le_mul_of_nonneg_left (hEm hR (hR.trans hRS) hRS) hc.le).trans hS
  exact le_antisymm (by nlinarith) (hEn R hR)

end DefocusingNLS

end OAI
