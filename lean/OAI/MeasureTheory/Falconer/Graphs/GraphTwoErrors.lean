import OAI.MeasureTheory.Falconer.Estimates.NonstationaryPower

namespace OAI

/-!
# Paying for both graph localization errors

The perpendicular error has an arbitrary derivative-order gain. The radial
error has an independent arbitrary Schwartz-decay order. Both pay for the
cap pairs, cell pairs and model-mass normalization with the same 11d cost.
-/

namespace Falconer

theorem graph_two_errors_absorption (d : ℕ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ) (minOrder : ℕ := 0) :
    ∃ m : ℕ, minOrder ≤ m ∧ ∀ {R K S P I A B C₁ C₂ q : ℝ},
      1 ≤ R → 0 ≤ K → 0 ≤ S → 0 ≤ P → 0 ≤ I → 0 ≤ A → 0 ≤ B →
      0 ≤ C₁ → 0 ≤ C₂ → 0 ≤ q →
      K ≤ A*R^d → S ≤ R^(2*d) → P*I ≤ R^(5*d) → q ≤ B*R^(-(26*σ)) →
      P*K^2*S^2*(I*(C₁*q^m+C₂*R^(-(T+(11*d : ℕ))))) ≤
        A^2*(C₁*B^m+C₂)*R^(-T) := by
  obtain ⟨m,hmin,hm⟩ := positive_power_gain_order_ge (by positivity : 0 < 26*σ) (↑(11*d : ℕ) : ℝ) T minOrder
  refine ⟨m,hmin,?_⟩
  intro R K S P I A B C₁ C₂ q hR hK hS hP hI hA hB hC₁ hC₂ hq hKbound hSbound hPI hqbound
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hcost : P*K^2*S^2*I ≤ A^2*R^(11*d) := by
    calc
      _ = (P*I)*K^2*S^2 := by ring
      _ ≤ R^(5*d)*(A*R^d)^2*(R^(2*d))^2 := by gcongr
      _ = A^2*(R^(5*d)*(R^d)^2*(R^(2*d))^2) := by ring
      _ = _ := by
        congr 1
        rw [← pow_mul,← pow_mul,← pow_add,← pow_add]
        congr 1
        omega
  have hgain : R^(11*d)*q^m ≤ B^m*R^(-T) := by
    simpa only [Real.rpow_natCast] using hm hR hB hq hqbound
  have hrad : R^(11*d)*R^(-(T+(11*d : ℕ))) = R^(-T) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hR0]
    congr 1
    ring
  calc
    _ = (P*K^2*S^2*I) * (C₁*q^m + C₂*R^(-(T+(11*d : ℕ)))) := by ring
    _ ≤ (A^2*R^(11*d)) * (C₁*q^m + C₂*R^(-(T+(11*d : ℕ)))) :=
      mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = A^2 * (C₁*(R^(11*d)*q^m) + C₂*(R^(11*d)*R^(-(T+(11*d : ℕ))))) := by ring
    _ ≤ A^2 * (C₁*(B^m*R^(-T)) + C₂*R^(-T)) := by rw [hrad]; gcongr
    _ = _ := by ring

end Falconer

end OAI
