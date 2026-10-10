import OAI.NumberTheory.Jacobsthal.Primes.DirichletZeroPenalty

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped ComplexOrder

noncomputable def characterPhase (n : ℕ) (t : ℝ) : ℂ := (n:ℂ)^(-(t:ℂ)*Complex.I)

lemma characterPhase_norm {n : ℕ} (hn : n ≠ 0) (t : ℝ) : ‖characterPhase n t‖ = 1 := by
  unfold characterPhase
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

lemma characterPhase_double {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    characterPhase n (2*t) = characterPhase n t ^ 2 := by
  unfold characterPhase
  rw [sq, ← Complex.cpow_add _ _ (by exact_mod_cast hn : (n:ℂ) ≠ 0)]
  congr 1
  push_cast
  ring

lemma twist_vonMangoldt_term_split {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (n : ℕ) :
    LSeries.term (fun k => chi k * (ArithmeticFunction.vonMangoldt k : ℂ))
      ((sigma:ℂ)+(t:ℂ)*Complex.I) n =
    LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (sigma:ℂ) n *
      chi n * characterPhase n t := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_add _ _ hnC]
    unfold characterPhase
    rw [neg_mul, Complex.cpow_neg]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

lemma character_positivity_polynomial (u : ℂ) (hu : ‖u‖ ≤ 1) :
    0 ≤ 3+4*u.re+(u^2).re := by
  have hsq : u.re^2+u.im^2 ≤ 1 := by
    have h := Complex.sq_norm u
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg u]
  simp only [pow_two, Complex.mul_re]
  nlinarith [sq_nonneg (1+u.re)]

lemma vonMangoldt_three_four_one_nonneg {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (n : ℕ) :
    0 ≤ (3 * LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (sigma:ℂ) n +
      4 * LSeries.term (fun k => chi k * (ArithmeticFunction.vonMangoldt k : ℂ))
        ((sigma:ℂ)+(t:ℂ)*Complex.I) n +
      LSeries.term (fun k => (chi^2) k * (ArithmeticFunction.vonMangoldt k : ℂ))
        ((sigma:ℂ)+(2*t:ℝ)*Complex.I) n).re := by
  by_cases hn : n = 0
  · simp [hn]
  · let a : ℂ := LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (sigma:ℂ) n
    let u : ℂ := chi n * characterPhase n t
    have hu : ‖u‖ ≤ 1 := by
      dsimp only [u]
      rw [norm_mul, characterPhase_norm hn, mul_one]
      exact chi.norm_le_one n
    have ha : 0 ≤ a := LSeries.term_nonneg
      (by exact_mod_cast (ArithmeticFunction.vonMangoldt_nonneg (n := n))) sigma
    have ha' := Complex.nonneg_iff.mp ha
    rw [twist_vonMangoldt_term_split, twist_vonMangoldt_term_split,
      characterPhase_double hn]
    have hp : (chi^2) n = (chi n)^2 := chi.pow_apply' (by decide) n
    rw [hp]
    have heq : 3*a+4*(a*chi n*characterPhase n t)+a*(chi n)^2*(characterPhase n t)^2 =
        a*(3+4*u+u^2) := by dsimp [u]; ring
    change 0 ≤ (3*a+4*(a*chi n*characterPhase n t)+a*(chi n)^2*(characterPhase n t)^2).re
    rw [heq, Complex.mul_re, ← ha'.2]
    simp only [zero_mul, sub_zero]
    apply mul_nonneg ha'.1
    simpa using character_positivity_polynomial u hu

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

lemma twisted_series_eq_actual_log_derivative {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => chi n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv (DirichletCharacter.LFunction chi) s / DirichletCharacter.LFunction chi s := by
  change LSeries ((fun n : ℕ => chi n) * (fun n => (ArithmeticFunction.vonMangoldt n:ℂ))) s = _
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hs,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi hs,
    ← DirichletCharacter.LFunction_eq_LSeries chi hs]

theorem character_log_derivative_positivity {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma t : ℝ) (hs : 1 < sigma) :
    0 ≤ 3 * (-deriv riemannZeta (sigma:ℂ) / riemannZeta (sigma:ℂ)).re +
      4 * (-deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
        DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)).re +
      (-deriv (DirichletCharacter.LFunction (chi^2)) ((sigma:ℂ)+(2*t:ℝ)*Complex.I) /
        DirichletCharacter.LFunction (chi^2) ((sigma:ℂ)+(2*t:ℝ)*Complex.I)).re := by
  let a := LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)) (sigma:ℂ)
  let b := LSeries.term (fun n => chi n * (ArithmeticFunction.vonMangoldt n:ℂ))
    ((sigma:ℂ)+(t:ℂ)*Complex.I)
  let c := LSeries.term (fun n => (chi^2) n * (ArithmeticFunction.vonMangoldt n:ℂ))
    ((sigma:ℂ)+(2*t:ℝ)*Complex.I)
  have ha : Summable a := ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hs)
  have hb : Summable b := DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi (by simpa using hs)
  have hc : Summable c := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (chi^2) (by simpa using hs)
  have hsum := ((ha.mul_left (3:ℂ)).add (hb.mul_left (4:ℂ))).add hc
  have hvalue := ((ha.hasSum.mul_left (3:ℂ)).add (hb.hasSum.mul_left (4:ℂ))).add hc.hasSum
  have hpositive : 0 ≤ (∑' n:ℕ, (3*a n+4*b n+c n)).re := by
    rw [Complex.re_tsum hsum]
    exact tsum_nonneg (fun n => vonMangoldt_three_four_one_nonneg chi sigma t n)
  rw [hvalue.tsum_eq] at hpositive
  change 0 ≤ (3 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)) (sigma:ℂ) +
    4 * LSeries (fun n => chi n * (ArithmeticFunction.vonMangoldt n:ℂ)) ((sigma:ℂ)+(t:ℂ)*Complex.I) +
    LSeries (fun n => (chi^2) n * (ArithmeticFunction.vonMangoldt n:ℂ)) ((sigma:ℂ)+(2*t:ℝ)*Complex.I)).re at hpositive
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs),
    twisted_series_eq_actual_log_derivative chi (by simpa using hs),
    twisted_series_eq_actual_log_derivative (chi^2) (by simpa using hs)] at hpositive
  simpa [Complex.add_re, Complex.mul_re] using hpositive

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
