import OAI.NumberTheory.TwoPointCorrelations.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Deriv

namespace OAI

/-! Exact logarithmic identities at the start of Halász's method. The
multiplicativity hypothesis here is complete multiplicativity on positive
arguments, as supplied by the corrected MRT reduction. -/

namespace TwoPointCorrelations

open Finset

theorem halasz_logarithmic_convolution (f : ℕ → ℂ)
    (hf : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (n : ℕ) :
    f n * (Real.log (n : ℝ) : ℂ) =
      ∑ d ∈ n.divisors,
        (ArithmeticFunction.vonMangoldt d : ℂ) * f d * f (n / d) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hterm (d : ℕ) (hd : d ∈ n.divisors) :
      (ArithmeticFunction.vonMangoldt d : ℂ) * f d * f (n / d) =
        (ArithmeticFunction.vonMangoldt d : ℂ) * f n := by
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn)
    have hquot : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn) hdpos
    rw [mul_assoc, ← hf d (n / d) hdpos hquot, Nat.mul_div_cancel' hdn]
  calc
    _ = (∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d : ℂ)) * f n := by
      rw [← Complex.ofReal_sum, ArithmeticFunction.vonMangoldt_sum]
      ring
    _ = _ := by rw [sum_mul]; exact sum_congr rfl hterm |>.symm

noncomputable def halaszDirichletPolynomial (f : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, LSeries.term f s n

theorem halaszDirichletPolynomial_hasDerivAt (f : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    HasDerivAt (halaszDirichletPolynomial f N)
      (-∑ n ∈ Icc 1 N, (Real.log (n : ℝ) : ℂ) * LSeries.term f s n) s := by
  change HasDerivAt (fun z => ∑ n ∈ Icc 1 N, LSeries.term f z n) _ s
  have h := HasDerivAt.fun_sum (fun n (_ : n ∈ Icc 1 N) => LSeries.hasDerivAt_term f n s)
  convert h using 1
  rw [sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  simp [hn0, mul_div_assoc]

end TwoPointCorrelations

end OAI
