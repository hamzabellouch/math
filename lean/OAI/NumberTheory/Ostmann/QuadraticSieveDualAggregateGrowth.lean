import OAI.NumberTheory.Ostmann.QuadraticSieveComplementAggregateGrowth

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem dual_aggregate_ambient_growth (δ σ : ℝ) (hδ : 0 < δ) (_hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P T : ℝ) (K N : ℕ),
      1 ≤ P → 0 ≤ T → T ≤ P^δ → 0 < K → 0 < N →
      (N:ℝ) ≤ P → (K:ℝ) ≤ P^3 →
      T^3*(2*(K:ℝ)*N)^δ*(N:ℝ)^δ*(K:ℝ)^δ*((N:ℝ)^2)^δ*
        (2*Real.sqrt 2*P^4)^σ ≤ C*P^(13*δ+4*σ) := by
  refine ⟨(2:ℝ)^δ*(2*Real.sqrt 2)^σ,by positivity,?_⟩
  intro P T K N hP hT hTP hK hN hNP hKP
  have hPp : 0 < P := by linarith
  have hKp : (0:ℝ) < K := by exact_mod_cast hK
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have ht : T^3 ≤ P^(3*δ) := by
    have hh := pow_le_pow_left₀ hT hTP 3
    rw [← Real.rpow_mul_natCast hPp.le] at hh
    simpa only [Nat.cast_ofNat, mul_comm δ] using hh
  have hk : (K:ℝ)^δ ≤ P^(3*δ) := by
    have hh := Real.rpow_le_rpow hKp.le hKP hδ.le
    rwa [← Real.rpow_natCast P 3,← Real.rpow_mul hPp.le] at hh
  have hn : (N:ℝ)^δ ≤ P^δ := Real.rpow_le_rpow hNp.le hNP hδ.le
  have hn2 : ((N:ℝ)^2)^δ ≤ P^(2*δ) := by
    have hh := Real.rpow_le_rpow (sq_nonneg (N:ℝ))
      (pow_le_pow_left₀ hNp.le hNP 2) hδ.le
    rwa [← Real.rpow_natCast P 2,← Real.rpow_mul hPp.le] at hh
  have hkn : (2*(K:ℝ)*N)^δ ≤ (2:ℝ)^δ*P^(4*δ) := by
    have hb : 2*(K:ℝ)*N ≤ 2*P^4 := by
      nlinarith [mul_le_mul hKP hNP hNp.le (by positivity)]
    have hh := Real.rpow_le_rpow (by positivity) hb hδ.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),
      ← Real.rpow_natCast P 4,← Real.rpow_mul hPp.le] at hh
    exact hh
  have hs : (2*Real.sqrt 2*P^4)^σ = (2*Real.sqrt 2)^σ*P^(4*σ) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast P 4,← Real.rpow_mul hPp.le]
    norm_num
  calc
    _ ≤ P^(3*δ)*((2:ℝ)^δ*P^(4*δ))*P^δ*P^(3*δ)*P^(2*δ)*
        ((2*Real.sqrt 2)^σ*P^(4*σ)) := by
      rw [hs]
      gcongr
    _ = ((2:ℝ)^δ*(2*Real.sqrt 2)^σ)*
        (P^(3*δ)*P^(4*δ)*P^δ*P^(3*δ)*P^(2*δ)*P^(4*σ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hPp,← Real.rpow_add hPp,← Real.rpow_add hPp,
        ← Real.rpow_add hPp,← Real.rpow_add hPp]
      congr 2
      ring

theorem dual_aggregate_ambient_loss (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η P T : ℝ) (K N : ℕ),
      0 < η → η ≤ ε/100 → 1 ≤ P → T = P^η →
      0 < K → 0 < N → (N:ℝ) ≤ P → (K:ℝ) ≤ P^3 →
      T^3*(2*(K:ℝ)*N)^(ε/100)*(N:ℝ)^(ε/100)*(K:ℝ)^(ε/100)*
        ((N:ℝ)^2)^(ε/100)*(2*Real.sqrt 2*P^4)^(ε/100) ≤ C*P^ε := by
  have hδ : 0 < ε/100 := by positivity
  obtain ⟨C,hC,hbound⟩ := dual_aggregate_ambient_growth (ε/100) (ε/100) hδ hδ
  refine ⟨C,hC,?_⟩
  intro η P T K N hη hηδ hP hT hK hN hNP hKP
  have ht0 : 0 ≤ T := by rw [hT]; positivity
  have ht : T ≤ P^(ε/100) := by
    rw [hT]
    exact Real.rpow_le_rpow_of_exponent_le hP hηδ
  exact (hbound P T K N hP ht0 ht hK hN hNP hKP).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP (by linarith)) hC.le)

theorem dual_aggregate_depth_loss (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η P : ℝ) (K N : ℕ),
      0 < η → η ≤ ε/100 → 1 ≤ P → 0 < K → 0 < N →
      (N:ℝ) ≤ P → (K:ℝ) ≤ P^3 →
      ((Nat.log 2 K+1:ℕ):ℝ)*((Nat.log 2 (N^2)+2:ℕ):ℝ)*
        (((2*K:ℕ):ℝ)*N)^(ε/100)*(N:ℝ)^(ε/100)*P^η ≤ C*P^ε := by
  have hδ : 0 < ε/100 := by positivity
  obtain ⟨C,hC,hbound⟩ := complement_aggregate_growth (ε/100) hδ
  refine ⟨C,hC,?_⟩
  intro η P K N hη hηδ hP hK hN hNP hKP
  have hPp : 0 < P := by linarith
  have ht : P^η ≤ (P^(ε/100))^3 := by
    rw [← Real.rpow_mul_natCast hPp.le]
    apply Real.rpow_le_rpow_of_exponent_le hP
    norm_num
    linarith
  have hh := hbound P K N hP hK hN hNP hKP
  have hp : P^(13*(ε/100)) ≤ P^ε :=
    Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  exact ((mul_le_mul_of_nonneg_left ht (by positivity)).trans hh).trans
    (mul_le_mul_of_nonneg_left hp hC.le)

end Ostmann.QuadraticSieve

end

end OAI
