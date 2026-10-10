import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateGrowth

namespace OAI

namespace Ostmann.QuadraticSieve

theorem dual_fourier_depth_loss (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η P T : ℝ) (K N : ℕ),
      0 < η → η ≤ ε/100 → 1 ≤ P → T = P^η →
      0 < K → 0 < N → (N : ℝ) ≤ P → (K : ℝ) ≤ P^3 →
      (Nat.log 2 K+1 : ℕ)*(Nat.log 2 (N^2)+2 : ℕ)*(2*(K : ℝ)*N)^(ε/100)*
        (N : ℝ)^(ε/100)*T^3*(2*Real.sqrt 2*P^4)^(ε/100) ≤ C*P^ε := by
  let δ : ℝ := ε/100
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,hgrowth⟩ := complement_aggregate_growth δ hδ
  refine ⟨C*(2*Real.sqrt 2)^δ,by positivity,?_⟩
  intro η P T K N hη hηδ hP hT hK hN hNP hKP
  have hPp : 0 < P := by linarith
  have ht0 : 0 ≤ T := by rw [hT]; positivity
  have ht : T ≤ P^δ := by
    rw [hT]
    exact Real.rpow_le_rpow_of_exponent_le hP hηδ
  have htc := pow_le_pow_left₀ ht0 ht 3
  have hg := hgrowth P K N hP hK hN hNP hKP
  have hf : (2*Real.sqrt 2*P^4)^δ = (2*Real.sqrt 2)^δ*P^(4*δ) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      ←Real.rpow_natCast P 4,←Real.rpow_mul hPp.le]
    norm_num
  calc
    _ ≤ ((Nat.log 2 K+1 : ℕ)*(Nat.log 2 (N^2)+2 : ℕ)*(2*(K : ℝ)*N)^δ*
        (N : ℝ)^δ*(P^δ)^3)*((2*Real.sqrt 2)^δ*P^(4*δ)) := by
      rw [←hf]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htc (by positivity)) (by positivity)
    _ ≤ (C*P^(13*δ))*((2*Real.sqrt 2)^δ*P^(4*δ)) :=
      mul_le_mul_of_nonneg_right hg (by positivity)
    _ = (C*(2*Real.sqrt 2)^δ)*P^(17*δ) := by
      calc
        _ = (C*(2*Real.sqrt 2)^δ)*(P^(13*δ)*P^(4*δ)) := by ring
        _ = _ := by rw [←Real.rpow_add hPp]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP (by dsimp [δ]; linarith)) (by positivity)

end Ostmann.QuadraticSieve

end OAI
