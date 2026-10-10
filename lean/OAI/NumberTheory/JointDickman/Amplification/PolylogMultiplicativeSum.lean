import OAI.NumberTheory.JointDickman.Arithmetic.PolylogPrimeHyperbola
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSquareErrorEstimate

namespace OAI

/-! # Rational minor-arc cancellation for squarefree-supported multiplicative sums -/
namespace JointDickman
open Finset

lemma prime_log_bilinear_as_product (f : ArithmeticFunction ℝ) (N : ℕ) (θ : ℝ) :
    primeLogBilinear f N θ =
      ∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p),
        (f p*Real.log p:ℂ)*(f m:ℂ)*additivePhase (θ*p*m) := by
  unfold primeLogBilinear
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro m hm
  simp only [Complex.ofReal_mul,Nat.cast_mul]
  rw [show (p:ℝ)*m*θ=θ*p*m by ring]
  ring

lemma prime_log_coefficient_bound (f : ArithmeticFunction ℝ) (hb : ∀ n, |f n| ≤ 1)
    (p : ℕ) : ‖(f p*Real.log p:ℂ)‖ ≤ Real.log p := by
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg p)]
  exact (mul_le_mul_of_nonneg_right (hb p) (Real.log_natCast_nonneg p)).trans_eq (one_mul _)

theorem prime_log_bilinear_polylog_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ) (N B q a : ℕ),
    (∀ n, |f n| ≤ 1) → 2 ≤ B → B^20 ≤ N → 0 < q → a.Coprime q →
    Real.log N ≤ 3*(B:ℝ) → (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^8 →
    ‖primeLogBilinear f N ((a:ℝ)/q)‖ ≤ C*N*(1+Real.log B) := by
  obtain ⟨C,hC,hbound⟩ := polylog_prime_hyperbola_bound
  refine ⟨C,hC,?_⟩
  intro f N B q a hb hB hBN hq ha hlog hqlo hqhi
  rw [prime_log_bilinear_as_product]
  apply hbound (fun p => (f p*Real.log p:ℂ)) (fun m => (f m:ℂ))
    N B q a hB hBN hq ha hlog hqlo hqhi
  · exact fun p _ => prime_log_coefficient_bound f hb p
  · intro m
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hb m

/-- A sufficient rational-frequency special case for the application.
This is proved from the bilinear decomposition, rather than assumed as MV77. -/
theorem squarefree_rational_polylog_sum_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
    (∀ n, ¬Squarefree n → f n=0) → ∀ (N B q a : ℕ),
    2 ≤ B → B^20 ≤ N → 0 < q → a.Coprime q → Real.log N ≤ 3*(B:ℝ) →
    (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^8 →
    ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*((a:ℝ)/q))‖ ≤
      C*N*(1+Real.log B)/Real.log N := by
  obtain ⟨C₀,hC₀,hreduce⟩ := squarefree_sum_prime_bilinear_bound
  obtain ⟨C₁,hC₁,hbilinear⟩ := prime_log_bilinear_polylog_bound
  refine ⟨C₀+C₁,by positivity,?_⟩
  intro f hf hb hs N B q a hB hBN hq ha hlog hqlo hqhi
  have hB0 : 0 < B := by omega
  have hN : 0 < N := lt_of_lt_of_le (pow_pos hB0 20) hBN
  have hN1 : (1:ℝ) < N := by
    have hpow : 1 < B^20 := Nat.one_lt_pow (by norm_num) hB
    exact_mod_cast hpow.trans_le hBN
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have h := hreduce f hf hb hs N hN ((a:ℝ)/q)
  have hbili := hbilinear f N B q a hb hB hBN hq ha hlog hqlo hqhi
  apply (le_div_iff₀ hlogN).mpr
  have hm : C₀*(N:ℝ) ≤ C₀*N*(1+Real.log B) := by
    nlinarith [mul_nonneg (mul_nonneg hC₀.le (Nat.cast_nonneg N)) hlogB]
  nlinarith

end JointDickman

end OAI
