import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMainComparison
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticTotientMain

namespace OAI

/-! # Identifying the original character weights in the main-term difference -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticRootCharacter (q w : ℕ) : ℂ :=
  (jacobiSym (w : ℤ) q : ℂ) / (Real.sqrt (w : ℝ) : ℂ)

 theorem quadraticRootCharacter_mul (q a b : ℕ) :
    quadraticRootCharacter q (a * b) = quadraticRootCharacter q a * quadraticRootCharacter q b := by
  unfold quadraticRootCharacter
  simp only [Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg a), Complex.ofReal_mul]
  exact (div_mul_div_comm _ _ _ _).symm

 theorem quadraticRootCharacter_square {D q u : ℕ} (hDq : D.Coprime q) (hu : u ∣ D) :
    quadraticRootCharacter q (u ^ 2) = (1 : ℂ) / u := by
  have hc : (u : ℤ).gcd q = 1 := hDq.of_dvd_left hu
  unfold quadraticRootCharacter
  simp only [Nat.cast_pow, jacobiSym.sq_one' hc, Int.cast_one,
    Real.sqrt_sq (Nat.cast_nonneg u), Complex.ofReal_natCast]

 theorem quadratic_root_square_moebius {D q : ℕ} (hD : D ≠ 0) (hDq : D.Coprime q) :
    (∑ u ∈ D.divisors, (ArithmeticFunction.moebius u : ℂ) * quadraticRootCharacter q (u ^ 2)) =
      (D.totient : ℂ) / D := by
  have hh := congrArg (fun x : ℝ => (x : ℂ)) (quadratic_totient_moebius D hD)
  push_cast at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [quadraticRootCharacter_square hDq (Nat.dvd_of_mem_divisors hu), mul_one_div]

 theorem quadratic_root_main_identity {D K q : ℕ} (hD : D ≠ 0) (hDq : D.Coprime q) :
    (∑ w ∈ Finset.Icc 1 (K * D ^ 2),
      (quadraticMainGamma D K w : ℂ) * quadraticRootCharacter q w) =
      (∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) * quadraticRootCharacter q e) *
        (∑ b ∈ oddSquarefreeRange K, quadraticRootCharacter q b) -
      ((D.totient : ℂ) / D) *
        ∑ v ∈ (oddSquarefreeRange K).filter (D.Coprime ·), quadraticRootCharacter q v := by
  rw [quadraticMainGamma_functional (Nat.pos_of_ne_zero hD)]
  simp_rw [quadraticRootCharacter_mul, ← Finset.mul_sum, ← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, quadratic_root_square_moebius hD hDq]

end Ostmann

end OAI
