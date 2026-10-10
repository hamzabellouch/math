import OAI.NumberTheory.TwoPoint.Halasz.HalaszExceptionalEnergy

namespace OAI

/-! Frequency translation and the actual typical-set coefficient. -/

namespace TwoPointCorrelations

open Finset
open scoped ComplexConjugate

lemma halasz_power_phase_frequency_add (t u x : ℝ) :
    halaszPowerPhase (t + u) x = halaszPowerPhase t x * halaszPowerPhase u x := by
  simp only [halaszPowerPhase, neg_add, add_mul, Complex.ofReal_add, Complex.exp_add]

lemma halasz_power_phase_twist (t : ℝ) (n : ℕ) :
    conj (mrtArchimedeanTwist t n) = halaszPowerPhase t n := by
  rw [mrtArchimedeanTwist, ← Complex.exp_conj]
  unfold halaszPowerPhase
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma halasz_twisted_phase_mean (F : ℕ → ℂ) (t u : ℝ) (N : ℕ) :
    halaszPhaseMean (halaszTwistedFunction F t) u N = halaszPhaseMean F (t + u) N := by
  unfold halaszPhaseMean
  apply sum_congr rfl
  intro n _
  rw [halaszTwistedFunction, halasz_power_phase_twist, halasz_power_phase_frequency_add]
  ring

lemma halasz_twisted_dyadic (F : ℕ → ℂ) (t u : ℝ) (N : ℕ) :
    mrtDyadicPolynomial (halaszTwistedFunction F t) N u = mrtDyadicPolynomial F N (t + u) := by
  rw [halasz_dyadic_phase, halasz_dyadic_phase]
  apply sum_congr rfl
  intro n _
  rw [halaszTwistedFunction, halasz_power_phase_twist, halasz_power_phase_frequency_add]
  ring

lemma halasz_typical_twist {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (F : ℕ → ℂ) (t : ℝ) :
    mrtTypicalCoefficient J P (halaszTwistedFunction F t) =
      halaszTwistedFunction (mrtTypicalCoefficient J P F) t := by
  funext n
  by_cases ht : mrtTypical J P n <;>
    simp [mrtTypicalCoefficient, halaszTwistedFunction, ht]

end TwoPointCorrelations

end OAI
