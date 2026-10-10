import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLargeDivisorTail
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMiddleFrequencyTail

namespace OAI

/-! # The full finite Poisson truncation, with every correction retained -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

noncomputable def quadraticPoissonError (q : ℕ) (ψ : 𝓢(ℝ, ℂ)) (X U V : ℝ) (L : ℕ) : ℂ :=
  (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U),
    (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeTail (𝓕 ψ) (X / d)) +
  (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
    (ArithmeticFunction.moebius d : ℂ) * quadraticLatticeTail ψ (d / X)) +
  ∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
    (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeOuter (𝓕 ψ) (X / d) L

noncomputable def quadraticPoissonCore (q : ℕ) (ψ : 𝓢(ℝ, ℂ)) (X U V : ℝ) (L : ℕ) : ℂ :=
  ((X : ℂ) * q.totient / q) * 𝓕 ψ 0 -
  ψ 0 * (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V), (ArithmeticFunction.moebius d : ℂ)) -
  𝓕 ψ 0 * (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
    (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ)) +
  ∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
    (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeWindow (𝓕 ψ) (X / d) L

private theorem moebius_high_low {q : ℕ} (_hq : q ≠ 0) (hq1 : q ≠ 1) (V : ℝ) :
    (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), (ArithmeticFunction.moebius d : ℂ)) =
      -(∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V), (ArithmeticFunction.moebius d : ℂ)) := by
  have htotal : (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ)) = 0 := by
    have hh := quadratic_moebius_divisor_sum q
    have hh' := congrArg (Int.cast : ℤ → ℂ) hh
    simpa only [hq1, ite_false, Int.cast_sum, Int.cast_zero] using hh'
  have hsplit :
      (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V), (ArithmeticFunction.moebius d : ℂ)) +
      (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), (ArithmeticFunction.moebius d : ℂ)) = 0 := by
    calc
      _ = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) := by
        rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : (d : ℝ) ≤ V
        · simp [hd, not_lt_of_ge hd]
        · simp [hd, lt_of_not_ge hd]
      _ = 0 := htotal
  exact eq_neg_of_add_eq_zero_right hsplit

 theorem quadratic_truncated_coprime_poisson {q : ℕ} [NeZero q] (hq1 : q ≠ 1)
    (ψ : 𝓢(ℝ, ℂ)) {X U V : ℝ} (hX : 0 < X) (hUV : U ≤ V) (L : ℕ) :
    (∑' n : ℤ, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) =
      quadraticPoissonCore q ψ X U V L + quadraticPoissonError q ψ X U V L := by
  rw [quadratic_coprime_main ψ hX, quadraticCoprimeRemainder_hybrid ψ hX hUV L]
  have hm := moebius_high_low (NeZero.ne q) hq1 V
  unfold quadraticPoissonCore quadraticPoissonError
  have hreplace : -(ψ 0 * (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
      (ArithmeticFunction.moebius d : ℂ))) =
      ψ 0 * (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℂ)) := by rw [hm, mul_neg]
  rw [sub_eq_add_neg _ (ψ 0 * _), hreplace]
  simp only [Finset.sum_filter, Finset.mul_sum]
  have heq (d : ℕ) :
      (if (d : ℝ) ≤ U then
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeTail (𝓕 ψ) (X / d)
      else if (d : ℝ) ≤ V then
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
          (quadraticLatticeWindow (𝓕 ψ) (X / d) L + quadraticLatticeOuter (𝓕 ψ) (X / d) L)
      else (ArithmeticFunction.moebius d : ℂ) *
        (ψ 0 + quadraticLatticeTail ψ (d / X) - ((X / d : ℝ) : ℂ) * 𝓕 ψ 0)) =
      ψ 0 * (if V < (d : ℝ) then (ArithmeticFunction.moebius d : ℂ) else 0) -
      𝓕 ψ 0 * (if V < (d : ℝ) then
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) else 0) +
      (if U < (d : ℝ) ∧ (d : ℝ) ≤ V then
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeWindow (𝓕 ψ) (X / d) L else 0) +
      ((if (d : ℝ) ≤ U then
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeTail (𝓕 ψ) (X / d) else 0) +
      (if V < (d : ℝ) then
        (ArithmeticFunction.moebius d : ℂ) * quadraticLatticeTail ψ (d / X) else 0) +
      (if U < (d : ℝ) ∧ (d : ℝ) ≤ V then
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * quadraticLatticeOuter (𝓕 ψ) (X / d) L else 0)) := by
    by_cases hdu : (d : ℝ) ≤ U
    · have hdv : (d : ℝ) ≤ V := hdu.trans hUV
      simp [hdu, hdv, not_lt_of_ge hdu, not_lt_of_ge hdv]
    · by_cases hdv : (d : ℝ) ≤ V
      · simp [hdu, hdv, lt_of_not_ge hdu, not_lt_of_ge hdv, mul_add]
      · simp [hdu, hdv, lt_of_not_ge hdu, lt_of_not_ge hdv, mul_add, mul_sub]
        ring
  have hsum := Finset.sum_congr (s₁ := q.divisors) rfl (fun d _ => heq d)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  linear_combination hsum

end Ostmann

end OAI
