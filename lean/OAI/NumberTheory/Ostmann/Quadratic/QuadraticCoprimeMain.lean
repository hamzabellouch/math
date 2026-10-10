import OAI.NumberTheory.Ostmann.Quadratic.QuadraticTotientMain

namespace OAI

/-! # Separating the exact main term in coprime Poisson summation -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

noncomputable def quadraticCoprimeRemainder (q : ℕ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) : ℂ :=
  ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
    ∑' n : ℤ, if n = 0 then 0 else 𝓕 ψ ((n : ℝ) * X / d)

 theorem quadratic_coprime_main {q : ℕ} [NeZero q]
    (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) =
      ((X : ℂ) * q.totient / q) * 𝓕 ψ 0 + quadraticCoprimeRemainder q ψ X := by
  have hs (d : ℕ) (hd : d ∈ q.divisors) :
      (∑' n : ℤ, 𝓕 ψ ((n : ℝ) * X / d)) = 𝓕 ψ 0 +
        ∑' n : ℤ, if n = 0 then 0 else 𝓕 ψ ((n : ℝ) * X / d) := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hnorm := quadratic_scaled_summable (𝓕 ψ) (div_pos hdR hX)
    have hsum : Summable (fun n : ℤ => 𝓕 ψ ((n : ℝ) * X / d)) := by
      apply Summable.of_norm
      simpa only [div_div_eq_mul_div] using hnorm
    simpa only [Int.cast_zero, zero_mul, zero_div] using hsum.tsum_eq_add_tsum_ite 0
  have hcoef : (∑ d ∈ q.divisors,
      (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ)) = (X : ℂ) * q.totient / q := by
    have ht := congrArg (fun x : ℝ => (x : ℂ)) (quadratic_totient_moebius q (NeZero.ne q))
    simp only [Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_intCast,
      Complex.ofReal_natCast] at ht
    calc
      _ = (X : ℂ) * ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) / d := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        push_cast
        ring
      _ = _ := by rw [ht]; ring
  rw [quadratic_coprime_poisson ψ hX]
  calc
    _ = ∑ d ∈ q.divisors,
        ((ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * 𝓕 ψ 0 +
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
          ∑' n : ℤ, if n = 0 then 0 else 𝓕 ψ ((n : ℝ) * X / d)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hs d hd, mul_add]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hcoef]
      rfl

end Ostmann

end OAI
