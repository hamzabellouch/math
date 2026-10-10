import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.AssignmentTester
import OAI.Combinatorics.IndependentSets.Repetition.CayleySampling

namespace OAI

noncomputable section
namespace IndependentSetsGames.Foundations.PCP.CayleySampling
open scoped BigOperators
open Finset
open IndependentSetsGames.Foundations.Hastad
variable {V D : Type*}

variable {I : Type*} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]

omit [DecidableEq I] in
theorem exists_true_of_ne_zero (s : Cube I) (hs : s ≠ fun _ => false) :
    ∃ i, s i = true := by
  by_contra h
  apply hs
  funext i
  cases hi : s i
  · rfl
  · exact False.elim (h ⟨i, hi⟩)

theorem expect_parity_samples (s : Cube I) (hs : s ≠ fun _ => false)
    (F : (D → Bool) → ℝ) :
    (𝔼 g : D → Cube I, F (fun d => AssignmentTester.parity s (g d))) =
      𝔼 b : D → Bool, F b := by
  obtain ⟨i, hi⟩ := exists_true_of_ne_zero s hs
  exact expect_boolean_samples (AssignmentTester.parity s) (AssignmentTester.flipAt i)
    (AssignmentTester.flipAt_twice i)
    (fun x => AssignmentTester.parity_flipAt s i x hi) F

theorem expect_walsh_samples (s : Cube I) (hs : s ≠ fun _ => false)
    (F : (D → ℝ) → ℝ) :
    (𝔼 g : D → Cube I, F (fun d => walsh s (g d))) =
      𝔼 b : D → Bool, F (fun d => bitSign (b d)) := by
  simpa only [AssignmentTester.bitSign_parity] using
    expect_parity_samples s hs (fun b => F (fun d => bitSign (b d)))

theorem expect_walsh_mean (s : Cube I) (hs : s ≠ fun _ => false) (F : ℝ → ℝ) :
    (𝔼 g : D → Cube I, F (𝔼 d, walsh s (g d))) =
      𝔼 b : D → Bool, F (𝔼 d, bitSign (b d)) :=
  expect_walsh_samples s hs (fun z => F (𝔼 d, z d))

end IndependentSetsGames.Foundations.PCP.CayleySampling

end

end OAI
