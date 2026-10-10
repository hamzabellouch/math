import OAI.Combinatorics.ExpectationThreshold.ProbabilityFinite
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# The numerical contradiction used in rounding

A nonnegative score bounded below by one quarter on an event of probability
at least nine tenths has expectation at least nine fortieths.
-/

namespace TalagrandThreshold

variable {Ω : Type*} [Fintype Ω]

theorem expectation_ge_nine_fortieths (μ : FiniteLaw Ω) (P : Ω → Prop)
    (Z : Ω → ℝ) (hZ : ∀ ω, 0 ≤ Z ω) (hprob : (9 / 10 : ℝ) ≤ μ.prob P)
    (hlower : ∀ ω, P ω → (1 / 4 : ℝ) ≤ Z ω) :
    (9 / 40 : ℝ) ≤ μ.expectation Z := by
  have hinclusion : μ.prob P ≤ μ.prob (fun ω => (1 / 4 : ℝ) ≤ Z ω) :=
    μ.prob_mono hlower
  have hmarkov := μ.prob_ge_le_expectation_div Z hZ
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hbound : (9 / 10 : ℝ) ≤ μ.expectation Z / (1 / 4 : ℝ) :=
    hprob.trans (hinclusion.trans hmarkov)
  calc
    (9 / 40 : ℝ) = (9 / 10 : ℝ) * (1 / 4 : ℝ) := by norm_num
    _ ≤ μ.expectation Z := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 4)).mp hbound

theorem rounding_expectation_contradiction (μ : FiniteLaw Ω) (P : Ω → Prop)
    (Z : Ω → ℝ) (hZ : ∀ ω, 0 ≤ Z ω) (hprob : (9 / 10 : ℝ) ≤ μ.prob P)
    (hlower : ∀ ω, P ω → (1 / 4 : ℝ) ≤ Z ω)
    (hupper : μ.expectation Z ≤ (1 / 10 : ℝ)) : False := by
  have h := (expectation_ge_nine_fortieths μ P Z hZ hprob hlower).trans hupper
  exact (by norm_num : ¬ ((9 / 40 : ℝ) ≤ 1 / 10)) h

end TalagrandThreshold

end OAI
