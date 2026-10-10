import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.BallLocalization
import OAI.Analysis.RieszRectifiability.Kernel.BoundedBoxContainment

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem local_height_data_on_balls {ι : Type*} [Fintype ι] {d : ℕ} (m : ℕ)
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (μ : Measure (Ambient d)) [SFinite μ] (f : Ambient d → ℝ)
    (hf : ∀ H, MemLp f 2 (μ.restrict (boundedProjectionRegion π (e 0) K H)))
    (henergy : ∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m f q.1 q.2)
      ((μ.restrict (boundedProjectionRegion π (e 0) K H)).prod
        (μ.restrict (boundedProjectionRegion π (e 0) K H)))) (R : ℝ) :
    MemLp f 2 (μ.restrict (ball (e 0) R)) ∧
      Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m f q.1 q.2)
        ((μ.restrict (ball (e 0) R)).prod (μ.restrict (ball (e 0) R))) := by
  obtain ⟨H, hH⟩ := (eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft R).exists
  refine ⟨MemLp.mono_measure (Measure.restrict_mono hH le_rfl) (hf H), ?_⟩
  apply (henergy H).mono_measure
  rw [Measure.prod_restrict, Measure.prod_restrict]
  exact Measure.restrict_mono (prod_mono hH hH) le_rfl

end

end RieszRectifiability

end OAI
