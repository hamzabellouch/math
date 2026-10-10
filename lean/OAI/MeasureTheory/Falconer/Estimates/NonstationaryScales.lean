import OAI.MeasureTheory.Falconer.Graphs.GraphNormalization

namespace OAI

/-!
# Scale gain for the angular integration by parts

Depths are normalized by `N`, so `2^p = R^(p/N)`
is represented by `R^p`. The hypotheses and constants are those of
`graph:range` and `graph:ibp-ratio`, without asymptotic notation.
-/

namespace Falconer

theorem graph_nonstationary_ratio_bound {R c₀ σ a p v L : ℝ}
    (hR : 1 ≤ R) (hc₀ : 0 < c₀) (hσ : 0 ≤ σ)
    (hh : p-a ≤ v-p+2*σ) (hL : L ≤ v-p+2*σ) (hq : 10*σ ≤ v-p) :
    (1 + R^σ * max 1 (R^(L-50*σ)) +
        (min c₀ (R^(a-p+10*σ)))⁻¹ + R^(-a) / R^(-p+30*σ)) /
      (R^v * R^(-p+30*σ)) ≤ (4+c₀⁻¹) * R^(-26*σ) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let t := R^(v-p+4*σ)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by linarith)
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have h₁ : R^σ ≤ t := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have h₂ : R^σ * R^(L-50*σ) ≤ t := by
    rw [← Real.rpow_add hR0]
    exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hsymbol : R^σ * max 1 (R^(L-50*σ)) ≤ t := by
    by_cases hx : 1 ≤ R^(L-50*σ)
    · simpa only [max_eq_right hx] using h₂
    · simpa only [max_eq_left (le_of_not_ge hx), mul_one] using h₁
  have hcInv : 0 ≤ c₀⁻¹ := inv_nonneg.mpr hc₀.le
  have hcap : (min c₀ (R^(a-p+10*σ)))⁻¹ ≤ c₀⁻¹ * t + t := by
    by_cases hc : c₀ ≤ R^(a-p+10*σ)
    · rw [min_eq_left hc]
      have hmul := mul_le_mul_of_nonneg_left ht hcInv
      linarith
    · rw [min_eq_right (le_of_not_ge hc), ← Real.rpow_neg hR0.le]
      have hpower : R^(-(a-p+10*σ)) ≤ t :=
        Real.rpow_le_rpow_of_exponent_le hR (by linarith)
      have hmul := mul_nonneg hcInv ht0
      linarith
  have hspatial : R^(-a) / R^(-p+30*σ) ≤ t := by
    rw [← Real.rpow_sub hR0]
    exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hnum : 1 + R^σ * max 1 (R^(L-50*σ)) +
      (min c₀ (R^(a-p+10*σ)))⁻¹ + R^(-a) / R^(-p+30*σ) ≤ (4+c₀⁻¹)*t := by
    nlinarith
  have hden : R^v * R^(-p+30*σ) = R^(v-p+30*σ) := by
    rw [← Real.rpow_add hR0]
    congr 1
    ring
  apply (div_le_div_of_nonneg_right hnum (by positivity)).trans_eq
  dsimp only [t]
  rw [hden, mul_div_assoc, ← Real.rpow_sub hR0]
  congr 2
  ring

theorem graph_radial_oscillation_size {R σ p v : ℝ} (hR : 1 ≤ R)
    (hq : 10*σ ≤ v-p) : R^(40*σ) ≤ R^v * R^(-p+30*σ) := by
  rw [← Real.rpow_add (zero_lt_one.trans_le hR)]
  exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)

end Falconer

end OAI
