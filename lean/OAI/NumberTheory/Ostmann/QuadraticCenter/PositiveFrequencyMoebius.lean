import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparation
import OAI.NumberTheory.Ostmann.QuadraticSieveSquareRemoval

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ArithmeticFunction.Moebius

theorem squarefree_moebius_eq_primeFactors_sign {n : ℕ} (hn : Squarefree n) :
    μ n = (-1 : ℤ) ^ n.primeFactors.card := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hn, ArithmeticFunction.cardFactors_apply,
    ← Nat.toFinset_factors, List.toFinset_card_of_nodup hn.nodup_primeFactorsList]

theorem coprime_indicator_squarefree_divisors {M : ℕ} (hM : Squarefree M) (w : ℕ) :
    (if w.Coprime M then (1 : ℂ) else 0) =
      ∑ P ∈ M.divisors, if P ∣ w then (-1 : ℂ) ^ P.primeFactors.card else 0 := by
  classical
  have hset : M.divisors.filter (fun P => P ∣ w) = (M.gcd w).divisors := by
    ext P
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hM.ne_zero,
      Nat.gcd_ne_zero_left hM.ne_zero]
  calc
    _ = ∑ P ∈ (M.gcd w).divisors, (μ P : ℂ) := by
      rw [QuadraticSieve.sum_moebius_divisors_complex]
      simp only [Nat.coprime_comm, Nat.Coprime]
    _ = ∑ P ∈ M.divisors, if P ∣ w then (μ P : ℂ) else 0 := by
      rw [← hset, Finset.sum_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P hP
      have hs := squarefree_moebius_eq_primeFactors_sign
        (hM.squarefree_of_dvd (Nat.dvd_of_mem_divisors hP))
      rw [hs]
      push_cast
      rfl

theorem positive_frequency_jacobi_square_factor (s v w M : ℕ) [NeZero M] :
    (jacobiSym ((s * v * w ^ 2 : ℕ) : ℤ) M : ℂ) =
      (jacobiSym (s : ℤ) M : ℂ) * (jacobiSym (v : ℤ) M : ℂ) *
        (if w.Coprime M then 1 else 0) := by
  have harg : ((s * v * w ^ 2 : ℕ) : ℤ) = (w : ℤ) ^ 2 * ((s : ℤ) * v) := by
    push_cast
    ring
  rw [harg, QuadraticSieve.jacobi_square_mul_left]
  simp only [Int.gcd_natCast_natCast, ← Nat.coprime_iff_gcd_eq_one]
  by_cases hc : w.Coprime M
  · rw [ite_eq_left hc, ite_eq_left hc, jacobiSym.mul_left, Int.cast_mul, mul_one]
  · simp only [ite_eq_right hc, Int.cast_zero, mul_zero]

theorem positive_frequency_jacobi_moebius (s v w : ℕ) {M : ℕ} (hM : Squarefree M) :
    (jacobiSym ((s * v * w ^ 2 : ℕ) : ℤ) M : ℂ) =
      (jacobiSym (s : ℤ) M : ℂ) * (jacobiSym (v : ℤ) M : ℂ) *
        ∑ P ∈ M.divisors, if P ∣ w then (-1 : ℂ) ^ P.primeFactors.card else 0 := by
  have : NeZero M := ⟨hM.ne_zero⟩
  rw [positive_frequency_jacobi_square_factor, coprime_indicator_squarefree_divisors hM]

theorem positive_frequency_square_sum_moebius (s v : ℕ) {M : ℕ} (hM : Squarefree M)
    (W : Finset ℕ) (F : ℕ → ℂ) :
    (∑ w ∈ W, (jacobiSym ((s * v * w ^ 2 : ℕ) : ℤ) M : ℂ) * F w) =
      (jacobiSym (s : ℤ) M : ℂ) * (jacobiSym (v : ℤ) M : ℂ) *
        ∑ P ∈ M.divisors, (-1 : ℂ) ^ P.primeFactors.card *
          ∑ w ∈ W.filter (fun w => P ∣ w), F w := by
  simp_rw [positive_frequency_jacobi_moebius s v _ hM]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 2
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs <;> simp

end Ostmann.QuadraticCenter

end

end OAI
