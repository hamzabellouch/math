import OAI.NumberTheory.EgyptianFractions.ThreePrimeLocalDensity
import OAI.NumberTheory.EgyptianFractions.ThreePrimeLocalFactor

namespace OAI
noncomputable section

namespace Problem337

/-- The normalized actual local solution count agrees with the zero frequency
plus the normalized cubic nonzero-frequency sum. -/
theorem threePrimeLocalFactor_eq_cubic (p u : ℕ) [Fact p.Prime] :
    (threePrimeLocalFactor p (u : ZMod p) : ℂ) =
      1 + ThreePrimeLocalFactor.cubicPrimeCoefficient p u := by
  have hp := (Fact.out : p.Prime)
  rw [threePrimeLocalFactor_natCast p u hp.two_le]
  exact (ThreePrimeLocalFactor.one_add_cubicPrimeCoefficient_eq_real p u hp).symm

/-- An unnormalized finite Fourier identity for literal local unit triples.
All normalizing constants are checked against the combinatorial count. -/
theorem threePrimeLocalTriples_card_fourier (p u : ℕ) [Fact p.Prime] :
    (p : ℂ) * (threePrimeLocalTriples p (u : ZMod p)).card =
      ((p : ℂ) - 1) ^ 3 *
        (1 + ThreePrimeLocalFactor.cubicPrimeCoefficient p u) := by
  have hp := (Fact.out : p.Prime)
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [threePrimeLocalTriples_card, ← threePrimeLocalFactor_eq_cubic]
  unfold threePrimeLocalFactor
  push_cast
  field_simp

/-- The cubic prime-frequency contribution is real, as follows from its
independently counted local-density interpretation. -/
theorem threePrimeCubicCoefficient_im (p u : ℕ) [Fact p.Prime] :
    (ThreePrimeLocalFactor.cubicPrimeCoefficient p u).im = 0 := by
  have h := congrArg Complex.im (threePrimeLocalFactor_eq_cubic p u)
  simpa using h.symm

end Problem337

end

end OAI
