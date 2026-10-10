import OAI.MeasureTheory.Falconer.Radial.RadialTestNorm
import OAI.MeasureTheory.Falconer.Graphs.FiberTrace

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem sourceTestNorm_angular_density_le (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    sourceTestNorm q (((volume.restrict (Ioc 0 (2*Real.pi))).withDensity g).map
      sourceUnitDirection) ≤
        (∫⁻ θ in Ioc 0 (2*Real.pi), (g θ)^p)^(1/p) := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  let ν : Measure ℝ := volume.restrict (Ioc 0 (2*Real.pi))
  let G : ℝ → ℝ≥0∞ := fun θ => ‖F (sourceUnitDirection θ)‖ₑ
  have hFc : Continuous (F ∘ sourceUnitDirection) :=
    F.continuous.comp continuous_sourceUnitDirection
  have hG : Measurable G := hFc.enorm.measurable
  have hq : (∫⁻ θ, (G θ)^q ∂ν)^(1/q) ≤ 1 := by
    rw [sourceArcLength,eLpNorm_map_measure F.continuous.aestronglyMeasurable
      continuous_sourceUnitDirection.measurable.aemeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
        ENNReal.ofReal_ne_top hFc.aestronglyMeasurable,
      ENNReal.toReal_ofReal hpq.symm.nonneg] at hF
    simpa only [Function.comp_apply,G,ν] using hF
  have hb := enorm_integral_le_lintegral_enorm
    (μ := (ν.withDensity g).map sourceUnitDirection) (fun ω => F ω)
  rw [← ofReal_norm,lintegral_map (by fun_prop) continuous_sourceUnitDirection.measurable,
    lintegral_withDensity_eq_lintegral_mul _ hg hG] at hb
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hg.aemeasurable hG.aemeasurable
  have hh' : (∫⁻ θ, g θ * G θ ∂ν) ≤ (∫⁻ θ, (g θ)^p ∂ν)^(1/p) := by
    exact hh.trans ((mul_le_mul_right hq _).trans_eq (mul_one _))
  exact hb.trans hh'

theorem sourceTestNorm_radial_density_rpow_le (a : Plane → ℝ≥0∞) (ha : Measurable a)
    {p q : ℝ} (hpq : p.HolderConjugate q) (x : Plane) :
    (sourceTestNorm q ((volume.withDensity a).map (sourceRadialUnit x)))^p ≤
      ∫⁻ θ in Ioc 0 (2*Real.pi), (sourceRadialDensity a x θ)^p := by
  rw [sourceRadialUnit_withDensity a ha x]
  have h := ENNReal.rpow_le_rpow (sourceTestNorm_angular_density_le
    (sourceRadialDensity a x) (measurable_sourceRadialDensity a ha x) hpq) hpq.nonneg
  rwa [← ENNReal.rpow_mul,one_div_mul_cancel hpq.pos.ne',ENNReal.rpow_one] at h

end PlanarFalconer

end OAI
