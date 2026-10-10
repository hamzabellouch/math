import OAI.Geometry.NodalSets.Elliptic.CorrugationRegimeBounds

namespace OAI

namespace Yau.Geometry
open Real Filter
open scoped Topology
noncomputable section

lemma corrugation_high_regime_lower {χ l J T : ℝ}
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hJ : 0 < J) (hT : 0 < T) (hreg : T < J*χ*l) :
    0 < χ ∧ 0 < l ∧ T/J ≤ χ ∧ T/J ≤ l := by
  have hp : T/J < χ*l := (div_lt_iff₀ hJ).mpr (by nlinarith)
  have hχl1 := mul_le_mul_of_nonneg_left hl1 hχ
  have hχl2 := mul_le_mul_of_nonneg_right hχ1 hl
  have ht := div_pos hT hJ
  refine ⟨by nlinarith,by nlinarith,?_,?_⟩ <;> nlinarith

lemma corrugation_fractional_factor {x : ℝ} (hx : 0 < x) :
    x^((7:ℝ)/8) = x*x^(-(1:ℝ)/8) := by
  calc
    _ = x^((1:ℝ)+(-(1:ℝ)/8)) := by norm_num
    _ = x^(1:ℝ)*x^(-(1:ℝ)/8) := Real.rpow_add hx _ _
    _ = _ := by rw [Real.rpow_one]

lemma corrugation_high_regime_products {χ l J T : ℝ}
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hJ : 0 < J) (hT : 0 < T) (hreg : T < J*χ*l) :
    χ^((7:ℝ)/8)*l ≤ (T/J)^(-(1:ℝ)/8)*(χ*l) ∧
    l^((7:ℝ)/8) ≤ (T/J)^(-(1:ℝ)/8)*l := by
  obtain ⟨hc,hlp,hcT,hlT⟩ := corrugation_high_regime_lower hχ hχ1 hl hl1 hJ hT hreg
  have h1 := Real.rpow_le_rpow_of_nonpos (div_pos hT hJ) hcT (by norm_num : -(1:ℝ)/8 ≤ 0)
  have h2 := Real.rpow_le_rpow_of_nonpos (div_pos hT hJ) hlT (by norm_num : -(1:ℝ)/8 ≤ 0)
  constructor
  · rw [corrugation_fractional_factor hc]
    have hh := mul_le_mul_of_nonneg_right h1 (mul_nonneg hχ hl)
    nlinarith
  · rw [corrugation_fractional_factor hlp]
    nlinarith [mul_le_mul_of_nonneg_right h2 hl]

def corrugationHighErrorRate (L T : ℝ) (k : ℕ) : ℝ :=
  (corrugationFrequency k*corrugationScale L k)⁻¹*(T/corrugationFrequency k)^(-(1:ℝ)/8) +
    (corrugationFrequency k*(corrugationScale L k)^2)⁻¹/T + (corrugationFrequency k)⁻¹ +
    (corrugationFrequency k*corrugationScale L k)⁻¹/T

def corrugationHighRadialRate (L T : ℝ) (k : ℕ) : ℝ :=
  (corrugationScale L k)^2*(T/corrugationFrequency k)^(-(1:ℝ)/8)

lemma corrugationHighErrorRate_bounds {χ l L T : ℝ} (hL : 0 < L) (hT : 0 < T) (k : ℕ)
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hreg : T < corrugationFrequency k*χ*l) :
    (corrugationScale L k)⁻¹*χ^((7:ℝ)/8)*l +
      (corrugationFrequency k*(corrugationScale L k)^2)⁻¹ + χ*l +
      (corrugationFrequency k*corrugationScale L k)⁻¹ ≤
        corrugationHighErrorRate L T k*(corrugationFrequency k*χ*l) ∧
    (corrugationScale L k)^2*l^((7:ℝ)/8) ≤ corrugationHighRadialRate L T k*l := by
  have hJ := corrugationFrequency_positive k
  have hR := corrugationScale_positive hL k
  obtain ⟨h1,h2⟩ := corrugation_high_regime_products hχ hχ1 hl hl1 hJ hT hreg
  have htinv : (1:ℝ) ≤ (corrugationFrequency k*χ*l)/T :=
    (one_le_div hT).mpr hreg.le
  constructor
  · unfold corrugationHighErrorRate
    have hb1 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hR.le)
    have hb2 := mul_le_mul_of_nonneg_left htinv
      (inv_nonneg.mpr (mul_nonneg hJ.le (sq_nonneg (corrugationScale L k))))
    have hb4 := mul_le_mul_of_nonneg_left htinv (inv_nonneg.mpr (mul_nonneg hJ.le hR.le))
    have he1 : (corrugationScale L k)⁻¹*((T/corrugationFrequency k)^(-(1:ℝ)/8)*(χ*l)) =
        ((corrugationFrequency k*corrugationScale L k)⁻¹*(T/corrugationFrequency k)^(-(1:ℝ)/8))*
          (corrugationFrequency k*χ*l) := by field_simp
    have he3 : χ*l = (corrugationFrequency k)⁻¹*(corrugationFrequency k*χ*l) := by field_simp
    rw [← mul_assoc] at hb1
    rw [he1] at hb1
    simp only [div_eq_mul_inv] at hb1 hb2 hb4 he3 ⊢
    nlinarith
  · unfold corrugationHighRadialRate
    have hh := mul_le_mul_of_nonneg_left h2 (sq_nonneg (corrugationScale L k))
    nlinarith

lemma corrugation_frequency_negative_fraction {T : ℝ} (hT : 0 < T) (k : ℕ) :
    (T/corrugationFrequency k)^(-(1:ℝ)/8) = T^(-(1:ℝ)/8)*((k:ℝ)+1) := by
  have he : (corrugationFrequency k)^(-(1:ℝ)/8) = ((k:ℝ)+1)⁻¹ := by
    rw [show -(1:ℝ)/8 = -((1:ℝ)/8) by ring,Real.rpow_neg (corrugationFrequency_positive k).le,
      corrugationFrequency_eighth]
  rw [Real.div_rpow hT.le (corrugationFrequency_positive k).le,he,div_eq_mul_inv,inv_inv]

lemma corrugationHighErrorRate_formula {L T : ℝ} (hL : L ≠ 0) (hT : 0 < T) (k : ℕ) :
    corrugationHighErrorRate L T k =
      (L⁻¹*T^(-(1:ℝ)/8))/((k:ℝ)+1)^5 + ((L^2)⁻¹/T)/((k:ℝ)+1)^4 +
      1/((k:ℝ)+1)^8 + (L⁻¹/T)/((k:ℝ)+1)^6 := by
  rw [corrugationHighErrorRate,corrugation_frequency_negative_fraction hT,
    (corrugation_scale_rate_identities hL k).2.1,(corrugation_scale_rate_identities hL k).2.2.1,
    corrugationFrequency]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma corrugationHighRadialRate_formula {L T : ℝ} (hT : 0 < T) (k : ℕ) :
    corrugationHighRadialRate L T k = (L^2*T^(-(1:ℝ)/8))/((k:ℝ)+1)^3 := by
  rw [corrugationHighRadialRate,corrugation_frequency_negative_fraction hT,corrugationScale_formula]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma corrugation_high_rates_tendsto {L T : ℝ} (hL : L ≠ 0) (hT : 0 < T) :
    Tendsto (corrugationHighErrorRate L T) atTop (𝓝 0) ∧
    Tendsto (corrugationHighRadialRate L T) atTop (𝓝 0) := by
  constructor
  · change Tendsto (fun k ↦ corrugationHighErrorRate L T k) atTop (𝓝 0)
    simp_rw [corrugationHighErrorRate_formula hL hT]
    have h1 := corrugation_power_reciprocal_tendsto (L⁻¹*T^(-(1:ℝ)/8)) (by norm_num : (5:ℕ) ≠ 0)
    have h2 := corrugation_power_reciprocal_tendsto ((L^2)⁻¹/T) (by norm_num : (4:ℕ) ≠ 0)
    have h3 := corrugation_power_reciprocal_tendsto 1 (by norm_num : (8:ℕ) ≠ 0)
    have h4 := corrugation_power_reciprocal_tendsto (L⁻¹/T) (by norm_num : (6:ℕ) ≠ 0)
    simpa using ((h1.add h2).add h3).add h4
  · change Tendsto (fun k ↦ corrugationHighRadialRate L T k) atTop (𝓝 0)
    simp_rw [corrugationHighRadialRate_formula hT]
    exact corrugation_power_reciprocal_tendsto _ (by norm_num)

end
end Yau.Geometry

end OAI
