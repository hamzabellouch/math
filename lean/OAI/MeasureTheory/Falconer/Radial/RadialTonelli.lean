import OAI.MeasureTheory.Falconer.Radial.RadialDensity

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

@[fun_prop] theorem continuous_sourceFrame_joint :
    Continuous (fun p : ℝ × (ℝ × ℝ) => sourceFrame p.1 p.2) := by
  have h : (fun p : ℝ × (ℝ × ℝ) => sourceFrame p.1 p.2) =
      fun p => p.2.1 • sourceNormal p.1 + p.2.2 • sourceDirection p.1 := by
    funext p
    exact sourceFrame_eq _ _ _
  rw [h]
  unfold sourceNormal
  fun_prop

@[fun_prop] theorem measurable_projectedDensity_joint (a : Plane → ℝ≥0∞)
    (ha : Measurable a) : Measurable (fun p : ℝ × ℝ => projectedDensity a p.1 p.2) := by
  have hc : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1,(p.1.2,p.2))) := by fun_prop
  have h : Measurable (fun p : (ℝ × ℝ) × ℝ => a (sourceFrame p.1.1 (p.1.2,p.2))) :=
    ha.comp (continuous_sourceFrame_joint.comp hc).measurable
  exact h.lintegral_prod_right'

@[fun_prop] theorem measurable_sourceRadialDensity_joint (a : Plane → ℝ≥0∞)
    (ha : Measurable a) : Measurable (fun p : Plane × ℝ => sourceRadialDensity a p.1 p.2) := by
  have h : Measurable (fun p : (Plane × ℝ) × ℝ =>
      ENNReal.ofReal p.2 * a (p.1.1 + p.2 • sourceDirection p.1.2)) := by fun_prop
  exact h.lintegral_prod_right'

theorem radial_density_integral_le_fibers (a : Plane → ℝ≥0∞) (ha : Measurable a)
    (β : Measure Plane) [IsFiniteMeasure β] {D p : ℝ} (hp : 0 ≤ p)
    (hbound : ∀ᵐ x ∂β, ∀ y, a y ≠ 0 → dist y x ≤ D) :
    (∫⁻ x, (∫⁻ θ in Ioc 0 (2*Real.pi), (sourceRadialDensity a x θ)^p) ∂β) ≤
      (ENNReal.ofReal D)^p *
        ∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ z, (projectedDensity a θ z)^p
          ∂projectedMeasure β θ := by
  have hm : Measurable (fun v : Plane × ℝ =>
      (projectedDensity a v.2 (sourceProjection v.2 v.1))^p) := by
    have hc : Continuous (fun v : Plane × ℝ => (v.2,sourceProjection v.2 v.1)) := by
      unfold sourceProjection
      fun_prop
    exact ((measurable_projectedDensity_joint a ha).comp hc.measurable).pow_const p
  calc
    _ ≤ ∫⁻ x, (∫⁻ θ in Ioc 0 (2*Real.pi),
        (ENNReal.ofReal D)^p * (projectedDensity a θ (sourceProjection θ x))^p) ∂β := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with x hx
      apply lintegral_mono
      intro θ
      have h := ENNReal.rpow_le_rpow (sourceRadialDensity_le a x hx θ) hp
      rwa [ENNReal.mul_rpow_of_nonneg _ _ hp] at h
    _ = ∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ x,
        (ENNReal.ofReal D)^p * (projectedDensity a θ (sourceProjection θ x))^p ∂β :=
      lintegral_lintegral_swap (measurable_const.mul hm).aemeasurable
    _ = (ENNReal.ofReal D)^p *
        ∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ x,
          (projectedDensity a θ (sourceProjection θ x))^p ∂β := by
      simp_rw [lintegral_const_mul' _ _
        (ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top)]
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro θ
      exact (lintegral_map ((measurable_projectedDensity a ha θ).pow_const p)
        (by unfold sourceProjection; fun_prop)).symm

end PlanarFalconer

end OAI
