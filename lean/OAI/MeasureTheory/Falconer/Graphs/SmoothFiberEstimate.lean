import OAI.MeasureTheory.Falconer.Graphs.FiberSlice
import OAI.MeasureTheory.Falconer.Radial.ProjectedDiameter

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal SchwartzMap FourierTransform

theorem eLpNorm_nonneg_rpow {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 0 < p) :
    (eLpNorm' f p μ)^p = ∫⁻ x, (ENNReal.ofReal (f x))^p ∂μ := by
  rw [eLpNorm'_eq_lintegral_enorm,← ENNReal.rpow_mul,
    one_div_mul_cancel hp.ne',ENNReal.rpow_one]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hf x)]

theorem smooth_fiber_integral_bound (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (β : Measure Plane) [IsFiniteMeasure β] {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hs1 : 1 < s) (hs2 : s < 2)
    (hD : 0 < D) (hupt : (2-s)*p < t)
    (hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D) (θ : ℝ) :
    (ENNReal.ofReal (sourceEnergyConstant 1 (2-s)))^(p/2) *
      (∫⁻ z : ℝ, (projectedDensity (fun x => ENNReal.ofReal (a x)) θ z)^p
        ∂projectedMeasure β θ) ≤
      (ENNReal.ofReal (D^(t-(2-s)*p)))^(1/2 : ℝ) *
        (rieszEnergyOn (projectedMeasure β θ) t)^(1/2 : ℝ) *
        (sourceSliceEnergy (sourceDensityMeasure a) s θ)^(p/2) := by
  have h := source_fiber_lp_bound (projectedMeasure β θ)
    (sourceSchwartzFiber a hc ha θ) (sourceSchwartzFiber_nonneg a hc ha hn θ)
    hpq (by linarith) (by linarith) hD hupt (projectedMeasure_diameter β hdiam θ)
  rw [show 1-(2-s) = s-1 by ring,sourceSchwartzFiber_sliceEnergy a hc ha hn θ s] at h
  have hr := ENNReal.rpow_le_rpow h hpq.nonneg
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg,
    ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg,
    ← ENNReal.rpow_mul,← ENNReal.rpow_mul,← ENNReal.rpow_mul,
    show (1/2:ℝ)*p = p/2 by ring,
    show (1/(2*p))*p = (1/2:ℝ) by field_simp [hpq.pos.ne'],
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hpq.pos).ne' ENNReal.ofReal_ne_top
      (sourceSchwartzFiber a hc ha θ).continuous.aestronglyMeasurable,
    ENNReal.toReal_ofReal hpq.nonneg,
    eLpNorm_nonneg_rpow _ _ (sourceSchwartzFiber_nonneg a hc ha hn θ) hpq.pos] at hr
  simpa only [sourceSchwartzFiber_density a hc ha hn θ,mul_assoc] using hr

end PlanarFalconer

end OAI
