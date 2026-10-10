import OAI.Geometry.CylinderCovering.Nilpotent.Finite
import OAI.Geometry.CylinderCovering.Nilpotent.RadialIntegral
import OAI.Geometry.CylinderCovering.Nilpotent.Cost

namespace OAI

noncomputable section
open Set MeasureTheory
open RuledApproximation

namespace CylinderCovering.Nilpotent

theorem truncatedLabels_eq_radial_image (k ρ : ℝ) :
    truncatedLabels k ρ = NilpotentRadialIntegral.radialMap ''
      NilpotentRadialIntegral.parameterRegion (height k) ρ := by
  ext b
  constructor
  · rintro ⟨p, t, hp, ht, htH, rfl⟩
    refine ⟨vec2 p t, ?_, rfl⟩
    exact ⟨abs_le.mp hp, ht, htH⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z 0, z 1, abs_le.mpr hz.1, hz.2.1, hz.2.2, rfl⟩

lemma angularWeight_continuous (k : ℝ) :
    Continuous (fun p => 1 / Real.sqrt (1 + k ^ 2 * speedSq p)) := by
  apply continuous_const.div
    (Real.continuous_sqrt.comp (continuous_const.add
      (continuous_const.mul continuous_speedSq)))
  intro p
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (sqrt_denominator_ge_one k p))

lemma physicalWeight_angularField {κ k : ℝ} (hκ : κ ^ 2 = k ^ 2) (b : Plane) :
    physicalWeight (Real.sqrt 2) (angularField κ b) =
      1 / Real.sqrt (1 + k ^ 2 * speedSq (b 0 / b 1)) := by
  unfold physicalWeight angularField
  simp only [vec2_apply_zero, vec2_apply_one, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hκ]
  congr 2
  unfold speedSq
  ring

lemma half_le_height {k : ℝ} (hk : 0 ≤ k) (p : ℝ) : 1 / 2 ≤ height k p := by
  have ha := a_nonneg p
  have hk3 := pow_nonneg hk 3
  unfold height
  nlinarith [mul_nonneg (sq_nonneg k) ha]

theorem truncatedLabels_weight_integral {κ k ρ : ℝ} (hk : 0 ≤ k)
    (hκ : κ ^ 2 = k ^ 2) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2) :
    (∫ b in truncatedLabels k ρ, physicalWeight (Real.sqrt 2) (angularField κ b)) =
      ∫ p in Icc (-1 : ℝ) 1,
        (height k p ^ 2 - ρ ^ 2) / (2 * Real.sqrt (1 + k ^ 2 * speedSq p)) := by
  simp_rw [physicalWeight_angularField hκ]
  rw [truncatedLabels_eq_radial_image]
  rw [NilpotentRadialIntegral.radial_integral (height k)
    (fun p => 1 / Real.sqrt (1 + k ^ 2 * speedSq p))
    (height_continuous k) (angularWeight_continuous k) hρ
    (fun p _ => hρhalf.trans (half_le_height hk p))]
  apply setIntegral_congr_fun measurableSet_Icc
  intro p _
  ring

theorem truncatedLabels_weight_integral_le {κ k ρ : ℝ} (hk : 0 ≤ k)
    (hκ : κ ^ 2 = k ^ 2) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2) :
    (∫ b in truncatedLabels k ρ, physicalWeight (Real.sqrt 2) (angularField κ b)) ≤ I k := by
  rw [truncatedLabels_weight_integral hk hκ hρ hρhalf]
  have hden : ∀ p, 0 < 2 * Real.sqrt (1 + k ^ 2 * speedSq p) := by
    intro p
    have hp := sqrt_denominator_ge_one k p
    positivity
  have hcont : Continuous (fun p =>
      (height k p ^ 2 - ρ ^ 2) / (2 * Real.sqrt (1 + k ^ 2 * speedSq p))) := by
    apply ((height_continuous k).pow 2 |>.sub continuous_const).div
      (continuous_const.mul (Real.continuous_sqrt.comp
        (continuous_const.add (continuous_const.mul continuous_speedSq))))
    exact fun p => (hden p).ne'
  unfold I
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_mono_on (ContinuousOn.integrableOn_compact isCompact_Icc hcont.continuousOn)
    (ContinuousOn.integrableOn_compact isCompact_Icc
      (continuous_integrand k).continuousOn) measurableSet_Icc
  intro p _
  unfold integrand
  exact div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg ρ)) (hden p).le

end CylinderCovering.Nilpotent

end

end OAI
