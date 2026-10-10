import OAI.MeasureTheory.Falconer.Estimates.SliceAverage
import OAI.MeasureTheory.Falconer.Radial.ProjectionMoment

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem radial_angular_holder (E S : ℝ → ℝ≥0∞) (hE : Measurable E) (hS : Measurable S)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), (E θ)^(1/2:ℝ) * (S θ)^(p/2)) ≤
      (∫⁻ θ in Ioc 0 (2*Real.pi), (E θ)^(1/(2-p)))^((2-p)/2) *
        (∫⁻ θ in Ioc 0 (2*Real.pi), S θ)^(p/2) := by
  have hp : 0 < p := by linarith
  have hd : 0 < 2-p := by linarith
  have hc : (2/(2-p)).HolderConjugate (2/p) := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact (lt_div_iff₀ hd).mpr (by linarith)
    · simp only [inv_div]
      ring
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict (Ioc 0 (2*Real.pi))) hc
    (hE.pow_const (1/2:ℝ)).aemeasurable (hS.pow_const (p/2)).aemeasurable
  simp only [Pi.mul_apply,← ENNReal.rpow_mul] at h
  have h₁ : (1/2:ℝ)*(2/(2-p)) = 1/(2-p) := by ring
  have h₂ : (p/2)*(2/p) = 1 := by field_simp
  have h₃ : 1/(2/(2-p)) = (2-p)/2 := by field_simp
  have h₄ : 1/(2/p) = p/2 := by field_simp
  simpa only [h₁,h₂,h₃,h₄,ENNReal.rpow_one] using h

theorem radial_mixed_energy_bound (α β : Measure Plane) [IsFiniteMeasure α]
    [IsFiniteMeasure β] {s t p : ℝ} (hs : 0 < s) (hs2 : s < 2) (ht : 0 < t)
    (hp1 : 1 < p) (hp2 : p < 2) (htr : t/(2-p) < 1) :
    (ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2) *
      (∫⁻ θ in Ioc 0 (2*Real.pi),
        (rieszEnergyOn (projectedMeasure β θ) t)^(1/2:ℝ) * (sourceSliceEnergy α s θ)^(p/2)) ≤
      (angularEnergyConstant (t/(2-p)))^((2-p)/2) *
        (rieszEnergy β t)^(1/2:ℝ) * (2 * rieszEnergy α s)^(p/2) := by
  have hp : 0 < p := by linarith
  have hd : 0 < 2-p := by linarith
  have hr : 1 < 1/(2-p) := (lt_div_iff₀ hd).mpr (by linarith)
  have hh := radial_angular_holder _ _ (measurable_projected_energy β t)
    (measurable_sourceSliceEnergy α s) hp1 hp2
  have hm := projection_energy_moment β ht hr (by simpa [div_eq_mul_inv] using htr)
  have hpow := ENNReal.rpow_le_rpow hm (by positivity : 0 ≤ (2-p)/2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (2-p)/2),
    ← ENNReal.rpow_mul] at hpow
  have hx : (1/(2-p))*((2-p)/2) = (1/2:ℝ) := by field_simp
  rw [hx,show t*(1/(2-p)) = t/(2-p) by ring] at hpow
  have h := mul_le_mul_right (hh.trans (mul_le_mul_left hpow _))
    ((ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2))
  calc
    _ ≤ _ := h
    _ = (angularEnergyConstant (t/(2-p)))^((2-p)/2) *
        (rieszEnergy β t)^(1/2:ℝ) *
        ((ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2) *
          (∫⁻ θ in Ioc 0 (2*Real.pi), sourceSliceEnergy α s θ)^(p/2)) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ p/2),
        source_slice_average_energy α hs hs2]

theorem finite_radial_mixed_of_ball_bounds (α β : Measure Plane) [IsFiniteMeasure α]
    [IsFiniteMeasure β] {s t p dα dβ Cα Cβ : ℝ}
    (hs : 0 < s) (hs2 : s < 2) (hsd : s < dα) (hα : BallBound α dα Cα)
    (ht : 0 < t) (htd : t < dβ) (hβ : BallBound β dβ Cβ)
    (hp1 : 1 < p) (hp2 : p < 2) (htr : t/(2-p) < 1) :
    (∫⁻ θ in Ioc 0 (2*Real.pi),
      (rieszEnergyOn (projectedMeasure β θ) t)^(1/2:ℝ) * (sourceSliceEnergy α s θ)^(p/2)) < ∞ := by
  have hd : 0 < 2-p := by linarith
  have hr : 1 < 1/(2-p) := (lt_div_iff₀ hd).mpr (by linarith)
  have hE := finite_projection_moment_of_ball_bound β ht htd hβ hr.le
    (by simpa [div_eq_mul_inv] using htr)
  have hS := finite_slice_average_of_ball_bound α hs hs2 hsd hα
  exact (radial_angular_holder _ _ (measurable_projected_energy β t)
    (measurable_sourceSliceEnergy α s) hp1 hp2).trans_lt
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hE.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by linarith) hS.ne))

end PlanarFalconer

end OAI
