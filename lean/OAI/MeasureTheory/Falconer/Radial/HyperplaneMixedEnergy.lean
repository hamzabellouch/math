import OAI.MeasureTheory.Falconer.Slicing.HyperplaneSliceEnergy
import OAI.MeasureTheory.Falconer.Radial.HyperplaneEnergy

namespace OAI

/-! Combining the actual projected pin energy and measurable source slice bound. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal

theorem hyperplane_mixed_energy_bound (n : ℕ) {s t p : ℝ}
    (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (ht : 0 < t)
    (hp1 : 1 < p) (hp2 : p < 2) (htr : t/(2-p) < n) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (α β : Measure (Space (n+1)))
      [IsFiniteMeasure α] [IsFiniteMeasure β],
      (∫⁻ w : Sphere (n+1),
        (rieszEnergyOn (hyperplaneProjectedMeasure β w) t)^(1/2 : ℝ) *
          (hyperplaneEnergyMajorant α s w)^(p/2) ∂sphereMeasure (n+1)) ≤
        C * (rieszEnergyOn β t)^(1/2 : ℝ) * (rieszEnergyOn α s)^(p/2) := by
  have hp : 0 < p := by linarith
  have hd : 0 < 2-p := by linarith
  have hr : 1 < 1/(2-p) := (lt_div_iff₀ hd).mpr (by linarith)
  obtain ⟨A,hA,hE⟩ := hyperplane_projected_energy_moment n ht hr
    (by simpa only [div_eq_mul_inv, one_mul] using htr)
  let c : ℝ≥0∞ := ENNReal.ofReal (sourceEnergyConstant (n+1) s)
  let K : ℝ≥0∞ := ENNReal.ofReal ((((n+1 : ℕ) : ℝ)*2^(n+1))/2)
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (sourceEnergyConstant_pos hs0 hsn)).ne'
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  let B : ℝ≥0∞ := c⁻¹*K
  have hB : B < ∞ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (bot_lt_iff_ne_bot.mpr hc0))
    ENNReal.ofReal_lt_top
  refine ⟨A^((2-p)/2) * B^(p/2), ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hA.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hB.ne), ?_⟩
  intro α β hα hβ
  have hS : (∫⁻ w : Sphere (n+1), hyperplaneEnergyMajorant α s w ∂sphereMeasure (n+1)) ≤
      B * rieszEnergyOn α s := by
    have h := mul_le_mul_right (hyperplaneEnergyMajorant_integral_bound α hs0 hs hsn) c⁻¹
    change c⁻¹ * (c * _) ≤ c⁻¹ * (K * _) at h
    rwa [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul, ← mul_assoc] at h
  have hc : (2/(2-p)).HolderConjugate (2/p) := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact (lt_div_iff₀ hd).mpr (by linarith)
    · simp only [inv_div]
      ring
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (sphereMeasure (n+1)) hc
    ((hyperplane_projected_energy_measurable β t).pow_const (1/2 : ℝ)).aemeasurable
    ((hyperplaneEnergyMajorant_measurable α hs).pow_const (p/2)).aemeasurable
  simp only [Pi.mul_apply, ← ENNReal.rpow_mul] at hh
  have he₁ : (1/2 : ℝ)*(2/(2-p)) = 1/(2-p) := by ring
  have he₂ : (p/2)*(2/p) = (1 : ℝ) := by field_simp
  have he₃ : 1/(2/(2-p)) = (2-p)/2 := by field_simp
  have he₄ : 1/(2/p) = p/2 := by field_simp
  simp only [he₁, he₂, he₃, he₄, ENNReal.rpow_one] at hh
  have hEp := ENNReal.rpow_le_rpow (hE β) (by positivity : 0 ≤ (2-p)/2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (2-p)/2),
    ← ENNReal.rpow_mul,
    show (1/(2-p))*((2-p)/2) = (1/2 : ℝ) by field_simp] at hEp
  have hSp := ENNReal.rpow_le_rpow hS (by positivity : 0 ≤ p/2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ p/2)] at hSp
  exact hh.trans ((mul_le_mul' hEp hSp).trans_eq (by ac_rfl))

end Falconer

end OAI
