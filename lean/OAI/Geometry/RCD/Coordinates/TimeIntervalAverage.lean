import OAI.Geometry.RCD.Coordinates.BilinearIntervalAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! # The interior time average and its actual derivative -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def timeIntervalAverage (u : ℝ → E) (h t : ℝ) : E :=
  (2*h)⁻¹ • ∫ s in (t-h)..(t+h), u s

omit [CompleteSpace E] in
theorem timeIntervalAverage_primitive (u : ℝ → E) (hu : Integrable u) (h t : ℝ) :
    timeIntervalAverage u h t =
      (2*h)⁻¹ • ((∫ s in (0:ℝ)..(t+h), u s)-(∫ s in (0:ℝ)..(t-h), u s)) := by
  rw [timeIntervalAverage,intervalIntegral.integral_interval_sub_left
    hu.intervalIntegrable hu.intervalIntegrable]

omit [CompleteSpace E] in
theorem timeIntervalAverage_continuous (u : ℝ → E) (hu : Integrable u) (h : ℝ) :
    Continuous (timeIntervalAverage u h) := by
  have hc := hu.continuous_primitive 0
  change Continuous (fun t => timeIntervalAverage u h t)
  simp_rw [timeIntervalAverage_primitive u hu]
  exact ((hc.comp (continuous_id.add continuous_const)).sub
    (hc.comp (continuous_id.sub continuous_const))).const_smul _

theorem timeIntervalAverage_hasDerivAt (u : ℝ → E) (hu : Integrable u) (h t : ℝ)
    (hp : ContinuousAt u (t+h)) (hm : ContinuousAt u (t-h)) :
    HasDerivAt (timeIntervalAverage u h) ((2*h)⁻¹ • (u (t+h)-u (t-h))) t := by
  have hp' := intervalIntegral.integral_hasDerivAt_right (a := 0) hu.intervalIntegrable
    hu.aestronglyMeasurable.stronglyMeasurableAtFilter hp
  have hm' := intervalIntegral.integral_hasDerivAt_right (a := 0) hu.intervalIntegrable
    hu.aestronglyMeasurable.stronglyMeasurableAtFilter hm
  have hplus := hp'.scomp t ((hasDerivAt_id t).add_const h)
  have hminus := hm'.scomp t ((hasDerivAt_id t).sub_const h)
  rw [show timeIntervalAverage u h = fun s => (2*h)⁻¹ •
    ((∫ q in (0:ℝ)..(s+h), u q)-(∫ q in (0:ℝ)..(s-h), u q)) from
      funext (timeIntervalAverage_primitive u hu h)]
  simpa only [Function.comp_def,id_eq,one_smul,Pi.smul_def,Pi.sub_def] using
    HasDerivAt.const_smul ((2*h)⁻¹) (hplus.sub hminus)

theorem positive_bilinear_timeIntervalAverage
    (P : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ x, 0 ≤ P x x)
    (hsymm : ∀ x y, P x y = P y x)
    (u : ℝ → E) {h : ℝ} (hh : 0 < h) (t : ℝ)
    (hu : IntegrableOn u (Icc (t-h) (t+h)))
    (hE : IntegrableOn (fun s => P (u s) (u s)) (Icc (t-h) (t+h))) :
    P (timeIntervalAverage u h t) (timeIntervalAverage u h t) ≤
      (2*h)⁻¹ * ∫ s in (t-h)..(t+h), P (u s) (u s) := by
  have hab : t-h < t+h := by linarith
  have he : t+h-(t-h) = 2*h := by ring
  simpa only [he,timeIntervalAverage,intervalIntegral.integral_of_le hab.le,
    ← integral_Icc_eq_integral_Ioc] using
    positive_bilinear_interval_average P hpos hsymm hab u hu hE

end RegularPointCoordinates

end

end OAI
