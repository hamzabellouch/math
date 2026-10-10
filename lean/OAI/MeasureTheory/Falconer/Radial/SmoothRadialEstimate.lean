import OAI.MeasureTheory.Falconer.Graphs.SmoothFiberEstimate
import OAI.MeasureTheory.Falconer.Radial.RadialTonelli
import OAI.MeasureTheory.Falconer.Radial.RadialMixedEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem smooth_radial_density_energy_bound (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (β : Measure Plane) [IsFiniteMeasure β] {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hs1 : 1 < s) (hs2 : s < 2)
    (hD : 0 < D) (hupt : (2-s)*p < t) (htp : t < 2-p)
    (hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y, a y ≠ 0 → dist y x ≤ D) :
    ((ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2) *
      (ENNReal.ofReal (sourceEnergyConstant 1 (2-s)))^(p/2)) *
      (∫⁻ x, (∫⁻ θ in Ioc 0 (2*Real.pi),
        (sourceRadialDensity (fun y => ENNReal.ofReal (a y)) x θ)^p) ∂β) ≤
      ((ENNReal.ofReal D)^p * (ENNReal.ofReal (D^(t-(2-s)*p)))^(1/2 : ℝ)) *
        ((angularEnergyConstant (t/(2-p)))^((2-p)/2) *
          (rieszEnergy β t)^(1/2 : ℝ) * (2*rieszEnergy (sourceDensityMeasure a) s)^(p/2)) := by
  let := sourceDensityMeasure_finite a hc ha.continuous hn
  let c₁ := (ENNReal.ofReal (sourceEnergyConstant 1 (2-s)))^(p/2)
  let c₂ := (ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2)
  let d := (ENNReal.ofReal (D^(t-(2-s)*p)))^(1/2 : ℝ)
  let F := fun θ => ∫⁻ z, (projectedDensity (fun y => ENNReal.ofReal (a y)) θ z)^p
    ∂projectedMeasure β θ
  let M := fun θ => (rieszEnergyOn (projectedMeasure β θ) t)^(1/2 : ℝ) *
    (sourceSliceEnergy (sourceDensityMeasure a) s θ)^(p/2)
  have hc₁ : c₁ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith [hpq.pos]) ENNReal.ofReal_ne_top
  have hd : d ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hf : c₁ * (∫⁻ θ in Ioc 0 (2*Real.pi), F θ) ≤
      d * ∫⁻ θ in Ioc 0 (2*Real.pi), M θ := by
    rw [← lintegral_const_mul' _ _ hc₁,← lintegral_const_mul' _ _ hd]
    apply lintegral_mono
    intro θ
    exact (smooth_fiber_integral_bound a hc ha hn β hpq hs1 hs2 hD hupt hdiam θ).trans_eq
      (by dsimp [d,M]; ac_rfl)
  have hr := radial_density_integral_le_fibers (fun y => ENNReal.ofReal (a y))
    ha.continuous.measurable.ennreal_ofReal β hpq.nonneg
    (hbound.mono (fun x hx y hy => hx y (by intro h; exact hy (by simp [h]))))
  have ht : 0 < t := (mul_pos (by linarith : 0 < 2-s) hpq.pos).trans hupt
  have hm := radial_mixed_energy_bound (sourceDensityMeasure a) β (by linarith) hs2 ht
    (Real.holderConjugate_iff.mp hpq).1 hp2 ((div_lt_one (by linarith : 0 < 2-p)).mpr htp)
  calc
    _ ≤ (c₂*c₁) * ((ENNReal.ofReal D)^p * ∫⁻ θ in Ioc 0 (2*Real.pi), F θ) :=
      mul_le_mul_right hr _
    _ = ((ENNReal.ofReal D)^p*c₂) * (c₁ * ∫⁻ θ in Ioc 0 (2*Real.pi), F θ) := by ac_rfl
    _ ≤ ((ENNReal.ofReal D)^p*c₂) * (d * ∫⁻ θ in Ioc 0 (2*Real.pi), M θ) :=
      mul_le_mul_right hf _
    _ = ((ENNReal.ofReal D)^p*d) * (c₂ * ∫⁻ θ in Ioc 0 (2*Real.pi), M θ) := by ac_rfl
    _ ≤ _ := mul_le_mul_right hm _

end PlanarFalconer

end OAI
