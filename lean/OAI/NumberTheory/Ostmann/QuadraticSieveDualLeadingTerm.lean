import OAI.NumberTheory.Ostmann.QuadraticSieveLeadingCoefficients

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped ArithmeticFunction.Moebius

theorem dualPoisson_leading_term (d q b : ℕ) [NeZero q]
    (hd : Odd d) (hq : Odd q) (hsq : Squarefree q) (hb : 0 < b)
    (M : ℝ) (hM : 0 < M) (I : ℂ) :
    (∑ e ∈ (2 * d).divisors, ∑ a ∈ signedSquarefreeMultipliers,
      (μ e : ℂ) * ((M / (e * q) : ℝ) : ℂ) *
        gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
        (jacobiSym ((e : ℤ) * a * (b : ℤ)) q : ℂ) * (1 / 2 : ℂ) *
        ((Nat.totient q : ℂ) / (q : ℂ)) * (Real.sqrt ((e : ℝ) * q / (M * b)) : ℂ) *
        ((1 - (Real.sign (a : ℝ) : ℂ) * Complex.I) / (Real.sqrt |(a : ℝ)| : ℂ)) * I) =
      (Real.sqrt (M / b) : ℂ) * ((Nat.totient q : ℂ) / (2 * q : ℕ)) *
        leadingDivisorCoefficient d q * (jacobiSym (b : ℤ) q : ℂ) * I := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_neZero q
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hqs : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hqr).ne'
  let C : ℂ := (Real.sqrt (M / b) : ℂ) * ((Nat.totient q : ℂ) / (2 * q : ℕ)) *
    (jacobiSym (b : ℤ) q : ℂ) * I / (Real.sqrt (q : ℝ) : ℂ)
  have hterm (e : ℕ) (he : e ∈ (2 * d).divisors) (a : ℤ) :
      (μ e : ℂ) * ((M / (e * q) : ℝ) : ℂ) *
        gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
        (jacobiSym ((e : ℤ) * a * (b : ℤ)) q : ℂ) * (1 / 2 : ℂ) *
        ((Nat.totient q : ℂ) / (q : ℂ)) * (Real.sqrt ((e : ℝ) * q / (M * b)) : ℂ) *
        ((1 - (Real.sign (a : ℝ) : ℂ) * Complex.I) / (Real.sqrt |(a : ℝ)| : ℂ)) * I =
      C * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
        ((μ e : ℂ) / (Real.sqrt (e : ℝ) : ℂ) * (jacobiSym ((e : ℤ) * a) q : ℂ) *
          (1 - (Real.sign (a : ℝ) : ℂ) * Complex.I) / (Real.sqrt |(a : ℝ)| : ℂ)) := by
    have hep : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_mem_divisors he
    have hscale : ((M / (e * q) : ℝ) : ℂ) * (Real.sqrt ((e : ℝ) * q / (M * b)) : ℂ) =
        (Real.sqrt (M / b) : ℂ) / ((Real.sqrt (e : ℝ) : ℂ) * (Real.sqrt (q : ℝ) : ℂ)) := by
      exact_mod_cast dual_leading_scale (e : ℝ) (q : ℝ) M (b : ℝ) hep hqr hM hbr
    rw [jacobiSym.mul_left, Int.cast_mul]
    calc
      _ = (((M / (e * q) : ℝ) : ℂ) * (Real.sqrt ((e : ℝ) * q / (M * b)) : ℂ)) *
          ((μ e : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
            (jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym (b : ℤ) q : ℂ) *
            (1 / 2 : ℂ) * ((Nat.totient q : ℂ) / (q : ℂ)) *
            ((1 - (Real.sign (a : ℝ) : ℂ) * Complex.I) / (Real.sqrt |(a : ℝ)| : ℂ)) * I) := by ring
      _ = _ := by
        rw [hscale]
        dsimp only [C]
        push_cast
        ring
  calc
    _ = ∑ e ∈ (2 * d).divisors, ∑ a ∈ signedSquarefreeMultipliers,
        C * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
          ((μ e : ℂ) / (Real.sqrt (e : ℝ) : ℂ) * (jacobiSym ((e : ℤ) * a) q : ℂ) *
            (1 - (Real.sign (a : ℝ) : ℂ) * Complex.I) / (Real.sqrt |(a : ℝ)| : ℂ)) := by
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.sum_congr rfl (fun a _ => hterm e he a)
    _ = C * (gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
        (∑ e ∈ (2 * d).divisors, ∑ a ∈ signedSquarefreeMultipliers,
          (μ e : ℂ) / (Real.sqrt (e : ℝ) : ℂ) * (jacobiSym ((e : ℤ) * a) q : ℂ) *
            (1 - (Real.sign (a : ℝ) : ℂ) * Complex.I) / (Real.sqrt |(a : ℝ)| : ℂ))) := by
      simp_rw [← Finset.mul_sum]
      ring
    _ = C * ((Real.sqrt (q : ℝ) : ℂ) * leadingDivisorCoefficient d q) := by
      rw [dual_leading_coefficient d q hd hq hsq]
    _ = _ := by
      dsimp only [C]
      field_simp

end Ostmann.QuadraticSieve

end OAI
