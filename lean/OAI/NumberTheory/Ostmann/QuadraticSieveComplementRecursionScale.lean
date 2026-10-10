import OAI.NumberTheory.Ostmann.QuadraticSieveRecursionNumerics

namespace OAI

namespace Ostmann.QuadraticSieve

theorem complement_divisor_scale {M B D P : ℝ} (hM : 0 < M) (hB : 0 < B)
    (hD : 0 < D) (hP : 0 < P) (hPD : P ≤ 2*D) :
    (Real.sqrt (M/B)/D)*Real.sqrt P ≤ 2*Real.sqrt (M/(B*P)) := by
  have hroot : Real.sqrt (M/B) = Real.sqrt P*Real.sqrt (M/(B*P)) := by
    rw [←Real.sqrt_mul hP.le]
    congr 1
    field_simp
  have hid : (Real.sqrt (M/B)/D)*Real.sqrt P = (P/D)*Real.sqrt (M/(B*P)) := by
    rw [hroot]
    have hs := Real.sq_sqrt hP.le
    calc
      _ = (Real.sqrt P)^2/D*Real.sqrt (M/(B*P)) := by ring
      _ = _ := by rw [hs]
  rw [hid]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact (div_le_iff₀ hD).mpr hPD

theorem complement_range_bootstrap_scale {M N B x H D d₁ d₂ Δ Q₁ Q₂ : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hx : 0 ≤ x) (hH : 0 ≤ H)
    (hD : 0 < D) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (hΔ : 1 ≤ Δ)
    (hP : d₁*d₂ ≤ 2*D) (htransition : Real.sqrt (M/B)/Δ ≤ d₁*d₂)
    (_hQ₁ : 0 ≤ Q₁) (hQ₂ : 0 ≤ Q₂)
    (h1 : Q₁ ≤ H*(x+N/d₁)) (h2 : Q₂ ≤ H*(x+N/d₂)) :
    (Real.sqrt (M/B)/D)*Real.sqrt ((d₁*d₂)*Q₁*Q₂) ≤
      2*H*(Real.sqrt (M/B)*x+Δ*N) := by
  have hd1 : 0 < d₁ := by linarith
  have hd2 : 0 < d₂ := by linarith
  have hprod : 0 < d₁*d₂ := mul_pos hd1 hd2
  have hrad : Real.sqrt (Q₁*Q₂) ≤ H*Real.sqrt ((x+N/d₁)*(x+N/d₂)) := by
    have h := Real.sqrt_le_sqrt (mul_le_mul h1 h2 hQ₂ (by positivity))
    have heq : (H*(x+N/d₁))*(H*(x+N/d₂)) = H^2*((x+N/d₁)*(x+N/d₂)) := by ring
    rw [heq,Real.sqrt_mul (sq_nonneg H),Real.sqrt_sq hH] at h
    exact h
  rw [mul_assoc (d₁*d₂) Q₁ Q₂,Real.sqrt_mul hprod.le]
  calc
    _ = ((Real.sqrt (M/B)/D)*Real.sqrt (d₁*d₂))*Real.sqrt (Q₁*Q₂) := by ring
    _ ≤ (2*Real.sqrt (M/(B*(d₁*d₂))))*
        (H*Real.sqrt ((x+N/d₁)*(x+N/d₂))) :=
      mul_le_mul (complement_divisor_scale hM hB hD hprod hP) hrad (Real.sqrt_nonneg _) (by positivity)
    _ = 2*H*(Real.sqrt (M/(B*(d₁*d₂)))*Real.sqrt ((x+N/d₁)*(x+N/d₂))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (recursion_E4 hM hN hB hx hd₁ hd₂ hΔ htransition) (by positivity)

end Ostmann.QuadraticSieve

end OAI
