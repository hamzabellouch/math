import OAI.Combinatorics.GraphThreshold.Resampling
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

/-! # Success and failure of a local resampling transition -/

noncomputable section

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

/-- The denominator is large enough and the retained fragment fits in the
halved integral capacity. -/
def LocalSuccess (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) (c b : B) : Prop :=
  Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (W ∪ A c) ∧
    (A b \ W).card ≤ m / 2

/-- A local failure is the complement of the actual local success event. -/
def LocalFailure (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) (c b : B) : Prop :=
  ¬ LocalSuccess ν A ρ m W c b

theorem localFailure_iff (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) (c b : B) :
    LocalFailure ν A ρ m W c b ↔
      resamplingZ ν A ρ (W ∪ A c) < Real.exp (-10 * (m : ℝ)) ∨
        m / 2 < (A b \ W).card := by
  simp only [LocalFailure, LocalSuccess, not_and_or, not_le]

theorem localFailure_iff_twice (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) (c b : B) :
    LocalFailure ν A ρ m W c b ↔
      resamplingZ ν A ρ (W ∪ A c) < Real.exp (-10 * (m : ℝ)) ∨
        m < 2 * (A b \ W).card := by
  rw [localFailure_iff]
  apply or_congr Iff.rfl
  omega

end LeanBlast.SecondKahnKalai

end

end OAI
