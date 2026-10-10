import OAI.MeasureTheory.Falconer.Estimates.NonstationaryScales

namespace OAI

/-!
# A finite derivative order pays for all graph summations

The polynomial cost of the spatial labels, cap pairs and model masses is
included in `outer`. The derivative order is chosen before `R` or any
cell, cap or endpoint symbol. Constants may depend on that fixed order.
-/

namespace Falconer

theorem positive_power_gain_order {γ : ℝ} (hγ : 0 < γ) (outer T : ℝ) :
    ∃ m : ℕ, ∀ {R K q : ℝ}, 1 ≤ R → 0 ≤ K → 0 ≤ q →
      q ≤ K*R^(-γ) → R^outer*q^m ≤ K^m*R^(-T) := by
  obtain ⟨m,hm⟩ := exists_nat_ge ((T+outer)/γ)
  have horder : T+outer ≤ γ*(m : ℝ) := by
    have h := (div_le_iff₀ hγ).mp hm
    nlinarith
  refine ⟨m,?_⟩
  intro R K q hR hK hq hbound
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  calc
    R^outer*q^m ≤ R^outer*(K*R^(-γ))^m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hbound m) (by positivity)
    _ = K^m*R^(outer-γ*(m : ℝ)) := by
      rw [mul_pow,← Real.rpow_mul_natCast hR0.le,← mul_assoc,mul_comm (R^outer),mul_assoc,
        ← Real.rpow_add hR0]
      congr 2
      ring
    _ ≤ K^m*R^(-T) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) (pow_nonneg hK m)

theorem graph_ibp_arbitrary_power {σ c₀ : ℝ} (hσ : 0 < σ) (hc₀ : 0 < c₀)
    (outer T : ℝ) :
    ∃ m : ℕ, ∀ {R a p v L : ℝ}, 1 ≤ R →
      p-a ≤ v-p+2*σ → L ≤ v-p+2*σ → 10*σ ≤ v-p →
      R^outer * ((1 + R^σ * max 1 (R^(L-50*σ)) +
        (min c₀ (R^(a-p+10*σ)))⁻¹ + R^(-a)/R^(-p+30*σ)) /
          (R^v*R^(-p+30*σ)))^m ≤ (4+c₀⁻¹)^m*R^(-T) := by
  obtain ⟨m,hm⟩ := positive_power_gain_order (by positivity : 0 < 26*σ) outer T
  refine ⟨m,?_⟩
  intro R a p v L hR hh hL hq
  exact hm hR (by positivity) (by positivity)
    (by simpa only [neg_mul] using graph_nonstationary_ratio_bound hR hc₀ hσ.le hh hL hq)

/-- The graph order can also cover the derivative budget required by the far step. -/
theorem positive_power_gain_order_ge {γ : ℝ} (hγ : 0 < γ) (outer T : ℝ)
    (minOrder : ℕ) :
    ∃ m : ℕ, minOrder ≤ m ∧ ∀ {R K q : ℝ}, 1 ≤ R → 0 ≤ K → 0 ≤ q →
      q ≤ K*R^(-γ) → R^outer*q^m ≤ K^m*R^(-T) := by
  obtain ⟨m,hm⟩ := positive_power_gain_order hγ outer T
  refine ⟨m+minOrder,by omega,?_⟩
  intro R K q hR hK hq hbound
  have hdecay : R^(-γ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have hqK : q ≤ K := hbound.trans (mul_le_of_le_one_right hK hdecay)
  calc
    _ = (R^outer*q^m)*q^minOrder := by rw [pow_add]; ring
    _ ≤ (K^m*R^(-T))*K^minOrder :=
      mul_le_mul (hm hR hK hq hbound) (pow_le_pow_left₀ hq hqK _)
        (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; ring

end Falconer

end OAI
