import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPrimitivePoisson
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCoprimePoisson

namespace OAI

/-! # The first transform with every original Mobius divisor retained -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

private theorem jacobi_norm_le (n : ℤ) (q : ℕ) : ‖(jacobiSym n q : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy n q with h | h | h <;> rw [h] <;> norm_num

theorem quadratic_coprime_jacobi_poisson {D q : ℕ} [NeZero D] [NeZero q]
    (hq : Squarefree q) (ho : Odd q) (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, (1 : DirichletCharacter ℂ D) (n : ZMod D) *
      (jacobiSym n q : ℂ) * ψ ((n : ℝ) / X)) =
    quadraticGaussMultiplier q *
      ∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
        ((X / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        ∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
          𝓕 ψ ((h : ℝ) * X / ((e : ℝ) * q)) := by
  have hs (e : ℕ) : Summable (fun n : ℤ => (ArithmeticFunction.moebius e : ℂ) *
      (if (e : ℤ) ∣ n then (jacobiSym n q : ℂ) * ψ ((n : ℝ) / X) else 0)) := by
    apply Summable.of_norm_bounded
      ((quadratic_scaled_summable ψ hX).mul_left ‖(ArithmeticFunction.moebius e : ℂ)‖)
    intro n
    split_ifs
    · simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right (jacobi_norm_le n q) (norm_nonneg _)).trans_eq (one_mul _))
        (norm_nonneg _)
    · simp only [mul_zero, norm_zero]
      positivity
  calc
    _ = ∑' n : ℤ, ∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
        (if (e : ℤ) ∣ n then (jacobiSym n q : ℂ) * ψ ((n : ℝ) / X) else 0) := by
      apply tsum_congr
      intro n
      rw [principal_character_moebius, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp [mul_assoc]
    _ = ∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
        ∑' n : ℤ, if (e : ℤ) ∣ n then (jacobiSym n q : ℂ) * ψ ((n : ℝ) / X) else 0 := by
      rw [Summable.tsum_finsetSum (fun e _ => hs e)]
      simp only [tsum_mul_left]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have he₀ := Nat.pos_of_mem_divisors he
      have heR : (0 : ℝ) < e := by exact_mod_cast he₀
      rw [quadratic_tsum_multiples he₀.ne']
      have hterm (n : ℤ) :
          (jacobiSym ((e : ℤ) * n) q : ℂ) * ψ (((e : ℤ) * n : ℤ) / X) =
            (jacobiSym (e : ℤ) q : ℂ) *
              ((jacobiSym n q : ℂ) * ψ ((n : ℝ) / (X / e))) := by
        rw [jacobiSym.mul_left, Int.cast_mul]
        have ha : (((e : ℤ) * n : ℤ) : ℝ) / X = (n : ℝ) / (X / e) := by
          push_cast
          field_simp
        rw [ha]
        ring
      simp_rw [hterm]
      rw [tsum_mul_left, quadratic_primitive_poisson_normalized hq ho ψ (div_pos hX heR)]
      have hfreq (h : ℤ) : (h : ℝ) * (X / e) / q = (h : ℝ) * X / ((e : ℝ) * q) := by ring
      simp_rw [hfreq]
      have hchars : (∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
          𝓕 ψ ((h : ℝ) * X / ((e : ℝ) * q))) =
          (jacobiSym (e : ℤ) q : ℂ) * ∑' h : ℤ, (jacobiSym h q : ℂ) *
            𝓕 ψ ((h : ℝ) * X / ((e : ℝ) * q)) := by
        simp only [jacobiSym.mul_left, Int.cast_mul, mul_assoc, tsum_mul_left]
      rw [hchars, div_div]
      ring

end Ostmann

end OAI
