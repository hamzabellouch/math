import OAI.NumberTheory.TwoPoint.Circuits.CircuitErrorCutoff
import OAI.NumberTheory.TwoPoint.Circuits.CircuitMixedLaw
import OAI.NumberTheory.TwoPoint.Circuits.CircuitApproximationDegree

namespace OAI

/-! Braverman's final finite expectation argument. The combinatorial
approximation and an L² approximation to its small error event imply a
one-sided bounded-independence comparison. -/

namespace TwoPointCorrelations

open scoped Classical

lemma exceptionalExtension_gap {n : ℕ} {F : BooleanCube n → ℝ}
    (hF : ∀ x, F x = 0 ∨ F x = 1) (E : BooleanCube n → Bool) (x : BooleanCube n) :
    |F x - exceptionalExtension F E x| ≤ if E x then (1 : ℝ) else 0 := by
  cases hE : E x
  · simp [exceptionalExtension, hE]
  · rcases hF x with h | h <;> simp [exceptionalExtension, hE, h]

theorem TWiseUniformDensity.approximation_lower {n p q t : ℕ}
    {g F P T : BooleanCube n → ℝ} {E : BooleanCube n → Bool}
    (hwise : TWiseUniformDensity g t) (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1)
    (hF : ∀ x, F x = 0 ∨ F x = 1)
    (hP : WalshDegreeLE P p) (hT : WalshDegreeLE T q) (ht : (p + q) + (p + q) ≤ t)
    (houtside : ∀ x, E x = false → P x = F x)
    {B δ ε : ℝ} (hB : 1 ≤ B) (hbound : ∀ x, |P x| ≤ B)
    (hE : (mixedCubeLaw g hg hmean).probability (fun x => E x = true) ≤ δ)
    (herror : cubeAverage (fun x => ((if E x then (1 : ℝ) else 0) - T x) ^ 2) ≤ ε) :
    cubeAverage F - (8 * δ + 2 * B ^ 2 * ε) ≤ cubeAverage (fun x => g x * F x) := by
  have hmix := mixedCubeLaw_exception_bounds g hg hmean (fun x => E x = true) hE
  have hU : cubeAverage (fun x => if E x then (1 : ℝ) else 0) ≤ 2 * δ := by
    convert hmix.2 using 1
    congr 1
    funext x
    by_cases h : E x = true <;> simp [h]
  have hG : cubeAverage (fun x => g x * (if E x then (1 : ℝ) else 0)) ≤ 2 * δ := by
    have hm := hmix.1
    rw [FiniteLaw.probability, cubeDensityLaw_average] at hm
    convert hm using 1
    congr 1
    funext x
    by_cases h : E x = true <;> simp [h]
  have hu : cubeAverage (fun x => |F x - exceptionalExtension F E x|) ≤ 2 * δ :=
    (cubeAverage_mono (exceptionalExtension_gap hF E)).trans hU
  have hm : cubeAverage (fun x => g x * |F x - exceptionalExtension F E x|) ≤ 2 * δ :=
    (cubeAverage_mono (fun x => mul_le_mul_of_nonneg_left
      (exceptionalExtension_gap hF E x) (hg x))).trans hG
  have hs := errorCutoffPolynomial_mean_sq hF houtside hB hbound hU herror
  have hdeg := ((errorCutoffPolynomial_degree hP hT).minorant).mono ht
  have hh := hwise.semiExact_lower hg (exceptionalExtension_boolean hF E)
    (errorCutoffPolynomial_zero houtside) hdeg hu hm hs
  convert hh using 1
  ring

end TwoPointCorrelations

end OAI
