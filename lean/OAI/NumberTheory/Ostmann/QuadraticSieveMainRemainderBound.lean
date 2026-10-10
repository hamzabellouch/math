import OAI.NumberTheory.Ostmann.QuadraticSieveMainRemainderCover
import OAI.NumberTheory.Ostmann.QuadraticSieveMainRemainderRows

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate

theorem mainRemainder_character_sum_le (K Δ : ℕ) (hK : 0 < K) (hΔ : 0 < Δ)
    (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, 0 < n ∧ Nat.Coprime n Δ) :
    ‖∑ w ∈ Finset.Ioc K (K * Δ ^ 2),
      ((mainRemainder K Δ w : ℂ) / (Real.sqrt (w : ℝ) : ℂ)) *
        coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (w : ℤ)‖ ≤
      (2 * (Δ.divisors.card : ℝ) ^ 2 / Real.sqrt (K : ℝ)) *
        ∑ r ∈ oddSquarefreeUpTo (K * Δ ^ 2),
          ‖coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (r : ℤ)‖ := by
  classical
  let R : ℕ → ℂ := fun w => coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (w : ℤ)
  let F : ℕ → ℝ := fun w => if K < w then ‖R w‖ / Real.sqrt (w : ℝ) else 0
  have hF (w : ℕ) : 0 ≤ F w := by dsimp only [F]; split_ifs <;> positivity
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hsK : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.mpr hKr
  have hfactor (s r : ℕ) (hs : s ∈ Δ.divisors) :
      F (s ^ 2 * r) ≤ ‖R r‖ / Real.sqrt (K : ℝ) := by
    have hrow : R (s ^ 2 * r) = R r := by
      simpa only [R, Nat.cast_mul, Nat.cast_pow] using
        coprimeProductDivisorJacobiRow_square S S a (fun n => conj (a n)) 1 Δ s
          (Nat.mem_divisors.mp hs).1 (r : ℤ) hS hS
    dsimp only [F]
    split_ifs with hw
    · rw [hrow]
      apply div_le_div_of_nonneg_left (norm_nonneg _) hsK
      exact Real.sqrt_le_sqrt (by exact_mod_cast hw.le)
    · positivity
  calc
    _ ≤ ∑ w ∈ Finset.Ioc K (K * Δ ^ 2),
        ‖((mainRemainder K Δ w : ℂ) / (Real.sqrt (w : ℝ) : ℂ)) * R w‖ := norm_sum_le _ _
    _ = ∑ w ∈ Finset.Ioc K (K * Δ ^ 2), (|mainRemainder K Δ w| : ℤ) * F w := by
      apply Finset.sum_congr rfl
      intro w hw
      have hwK := (Finset.mem_Ioc.mp hw).1
      simp only [norm_mul, norm_div, Complex.norm_intCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), F, ite_eq_left hwK,
        Int.cast_abs]
      ring
    _ ≤ 2 * (Δ.divisors.card : ℝ) *
        ∑ s ∈ Δ.divisors, ∑ r ∈ oddSquarefreeUpTo (K * Δ ^ 2), F (s ^ 2 * r) :=
      mainRemainder_sum_le_squarefree K Δ hΔ F hF
    _ ≤ 2 * (Δ.divisors.card : ℝ) *
        ∑ s ∈ Δ.divisors, ∑ r ∈ oddSquarefreeUpTo (K * Δ ^ 2),
          ‖R r‖ / Real.sqrt (K : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro s hs
      exact Finset.sum_le_sum (fun r _ => hfactor s r hs)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div]
      dsimp only [R]
      ring

end Ostmann.QuadraticSieve

end OAI
