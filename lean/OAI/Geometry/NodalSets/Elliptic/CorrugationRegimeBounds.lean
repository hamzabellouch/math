import Mathlib.Tactic.Linarith
import OAI.Geometry.NodalSets.Elliptic.CorrugationFrequencyScale

namespace OAI

namespace Yau.Geometry
open Real Filter
open scoped Topology
noncomputable section

lemma corrugation_fractional_product {χ l : ℝ} (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) :
    χ^((7:ℝ)/8)*l ≤ (χ*l)^((7:ℝ)/8) ∧
    χ*l^((7:ℝ)/8) ≤ (χ*l)^((7:ℝ)/8) := by
  rw [Real.mul_rpow hχ hl]
  exact ⟨mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one hl hl1 (by norm_num)) (Real.rpow_nonneg hχ _),
    mul_le_mul_of_nonneg_right (Real.self_le_rpow_of_le_one hχ hχ1 (by norm_num)) (Real.rpow_nonneg hl _)⟩

lemma corrugation_low_regime_products {χ l J T : ℝ}
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hJ : 0 < J) (hreg : J*χ*l ≤ T) :
    χ^((7:ℝ)/8)*l ≤ (T/J)^((7:ℝ)/8) ∧
    χ*l^((7:ℝ)/8) ≤ (T/J)^((7:ℝ)/8) ∧ χ*l ≤ T/J := by
  have hp : χ*l ≤ T/J := (le_div_iff₀ hJ).mpr (by nlinarith)
  have hr := Real.rpow_le_rpow (mul_nonneg hχ hl) hp (by norm_num : (0:ℝ) ≤ 7/8)
  exact ⟨(corrugation_fractional_product hχ hχ1 hl hl1).1.trans hr,
    (corrugation_fractional_product hχ hχ1 hl hl1).2.trans hr,hp⟩

def corrugationLowErrorRate (L T : ℝ) (k : ℕ) : ℝ :=
  (corrugationScale L k)⁻¹*(T/corrugationFrequency k)^((7:ℝ)/8) +
    (corrugationFrequency k*(corrugationScale L k)^2)⁻¹ + T/corrugationFrequency k +
    (corrugationFrequency k*corrugationScale L k)⁻¹

def corrugationLowRadialRate (L T : ℝ) (k : ℕ) : ℝ :=
  (corrugationScale L k)^2*corrugationFrequency k*(T/corrugationFrequency k)^((7:ℝ)/8)

lemma corrugationLowErrorRate_bounds {χ l L : ℝ} (hL : 0 < L) (T : ℝ) (k : ℕ)
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hreg : corrugationFrequency k*χ*l ≤ T) :
    (corrugationScale L k)⁻¹*χ^((7:ℝ)/8)*l +
      (corrugationFrequency k*(corrugationScale L k)^2)⁻¹ + χ*l +
      (corrugationFrequency k*corrugationScale L k)⁻¹ ≤ corrugationLowErrorRate L T k ∧
    (corrugationScale L k)^2*corrugationFrequency k*χ*l^((7:ℝ)/8) ≤
      corrugationLowRadialRate L T k := by
  obtain ⟨h1,h2,h3⟩ := corrugation_low_regime_products hχ hχ1 hl hl1 (corrugationFrequency_positive k) hreg
  constructor
  · unfold corrugationLowErrorRate
    have hh := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (corrugationScale_positive hL k).le)
    nlinarith
  · unfold corrugationLowRadialRate
    have hh := mul_le_mul_of_nonneg_left h2
      (mul_nonneg (sq_nonneg (corrugationScale L k)) (corrugationFrequency_positive k).le)
    nlinarith

lemma corrugation_frequency_fraction {T : ℝ} (hT : 0 ≤ T) (k : ℕ) :
    (T/corrugationFrequency k)^((7:ℝ)/8) = T^((7:ℝ)/8)/((k:ℝ)+1)^7 := by
  rw [Real.div_rpow hT (corrugationFrequency_positive k).le,corrugationFrequency,
    ← Real.rpow_natCast ((k:ℝ)+1) 8,← Real.rpow_mul (by positivity)]
  norm_num

lemma corrugationLowErrorRate_formula {L T : ℝ} (hL : L ≠ 0) (hT : 0 ≤ T) (k : ℕ) :
    corrugationLowErrorRate L T k =
      (L⁻¹*T^((7:ℝ)/8))/((k:ℝ)+1)^5 + (L^2)⁻¹/((k:ℝ)+1)^4 +
      T/((k:ℝ)+1)^8 + L⁻¹/((k:ℝ)+1)^6 := by
  rw [corrugationLowErrorRate,corrugation_frequency_fraction hT,
    (corrugation_scale_rate_identities hL k).2.1,(corrugation_scale_rate_identities hL k).2.2.1,
    corrugationScale_formula,corrugationFrequency]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma corrugationLowRadialRate_formula {L T : ℝ} (hT : 0 ≤ T) (k : ℕ) :
    corrugationLowRadialRate L T k = (L^2*T^((7:ℝ)/8))/((k:ℝ)+1)^3 := by
  rw [corrugationLowRadialRate,corrugation_frequency_fraction hT,corrugationScale_formula,corrugationFrequency]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma corrugation_low_rates_tendsto {L T : ℝ} (hL : L ≠ 0) (hT : 0 ≤ T) :
    Tendsto (corrugationLowErrorRate L T) atTop (𝓝 0) ∧
    Tendsto (corrugationLowRadialRate L T) atTop (𝓝 0) := by
  constructor
  · change Tendsto (fun k ↦ corrugationLowErrorRate L T k) atTop (𝓝 0)
    simp_rw [corrugationLowErrorRate_formula hL hT]
    have h1 := corrugation_power_reciprocal_tendsto (L⁻¹*T^((7:ℝ)/8)) (by norm_num : (5:ℕ) ≠ 0)
    have h2 := corrugation_power_reciprocal_tendsto (L^2)⁻¹ (by norm_num : (4:ℕ) ≠ 0)
    have h3 := corrugation_power_reciprocal_tendsto T (by norm_num : (8:ℕ) ≠ 0)
    have h4 := corrugation_power_reciprocal_tendsto L⁻¹ (by norm_num : (6:ℕ) ≠ 0)
    simpa using ((h1.add h2).add h3).add h4
  · change Tendsto (fun k ↦ corrugationLowRadialRate L T k) atTop (𝓝 0)
    simp_rw [corrugationLowRadialRate_formula hT]
    exact corrugation_power_reciprocal_tendsto _ (by norm_num)

end
end Yau.Geometry

end OAI
