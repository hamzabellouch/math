import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.BallLocalization
import OAI.Analysis.RieszRectifiability.Kernel.BoundedBoxContainment

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem uniform_ball_moments_from_box_moments {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ℕ) (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (μ : ℕ → Measure (Ambient d)) (C : ℝ) (hg : ∀ j, GlobalUpperGrowth m C (μ j))
    (w : ℕ → Ambient d → ℝ)
    (hw : ∀ H j, MemLp (w j) 2 ((μ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B : ℕ → ℝ)
    (hB : ∀ H j, (∫ x, w j x ^ 2 ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B H)
    (R : ℝ) (hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j,
      ((μ j).restrict (ball (e 0) R)).real univ ≤ M ∧
      MemLp (w j) 2 ((μ j).restrict (ball (e 0) R)) ∧
      (∫ x in ball (e 0) R, w j x ^ 2 ∂μ j) ≤ M := by
  obtain ⟨H, hH⟩ := (eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft R).exists
  let M := max 0 (max (C * R ^ m) (B H))
  refine ⟨M, le_max_left _ _, fun j => ⟨?_, ?_, ?_⟩⟩
  · exact (ball_restriction_mass_bound m C (μ j) (hg j) (e 0) R hR).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact MemLp.mono_measure (Measure.restrict_mono hH le_rfl) (hw H j)
  · calc
      _ ≤ ∫ x, w j x ^ 2 ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H) :=
        integral_mono_measure (Measure.restrict_mono hH le_rfl)
          (Eventually.of_forall (fun x => sq_nonneg (w j x))) (hw H j).integrable_sq
      _ ≤ B H := hB H j
      _ ≤ M := (le_max_right _ _).trans (le_max_right _ _)

end

end RieszRectifiability

end OAI
