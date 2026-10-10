import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateZeroLargeWeights

namespace OAI

namespace Ostmann.QuadraticSieve

theorem dual_zero_large_outer_bound {Δ : ℕ} (hΔ : 0<Δ)
    (F : ℕ → ℤ → ℂ) (A : ℤ → ℝ) (hA : ∀ s,0≤A s) {B : ℝ} (hB : 0≤B)
    (hF : ∀ e ∈ (2*Δ).divisors, ∀ s ∈ signedSquarefreeMultipliers, ‖F e s‖≤A s*B) :
    ‖∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers,F e s‖ ≤
      (2*(1+∑ s ∈ signedSquarefreeMultipliers,A s))*(Δ:ℝ)^2*B := by
  have hsum : 0≤∑ s ∈ signedSquarefreeMultipliers,A s := Finset.sum_nonneg (fun s hs => hA s)
  have hΔ1 : (1:ℝ)≤Δ := by exact_mod_cast hΔ
  have hcard : ((2*Δ).divisors.card:ℝ)≤2*(Δ:ℝ)^2 := by
    have h : ((2*Δ).divisors.card:ℝ)≤(2*Δ:ℕ) := by exact_mod_cast Nat.card_divisors_le_self (2*Δ)
    push_cast at h
    nlinarith
  calc
    _ ≤ ∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers,A s*B := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e he
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun s hs => hF e he s hs))
    _ = ((2*Δ).divisors.card:ℝ)*(∑ s ∈ signedSquarefreeMultipliers,A s)*B := by
      simp only [← Finset.sum_mul,Finset.sum_const,nsmul_eq_mul]
    _ ≤ (2*(Δ:ℝ)^2)*(1+∑ s ∈ signedSquarefreeMultipliers,A s)*B := by gcongr; linarith
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
