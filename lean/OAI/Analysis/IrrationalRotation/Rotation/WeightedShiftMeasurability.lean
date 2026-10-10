import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftPowers
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X]

theorem stronglyMeasurable_iff_coordinates (ξ : X → Hilbert) :
    StronglyMeasurable ξ ↔ ∀ k : ℤ, StronglyMeasurable (fun x => ξ x k) := by
  constructor
  · intro h k
    exact (lp.lipschitzWith_one_eval 2 k).continuous.comp_stronglyMeasurable h
  · intro h
    apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ℤ))
      (f := fun s x => ∑ k ∈ s, lp.single 2 k (ξ x k))
    · intro s
      simpa only [lp.singleContinuousLinearMap_apply] using
        s.stronglyMeasurable_fun_sum (fun k _ =>
          (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 k).continuous.comp_stronglyMeasurable (h k))
    · apply tendsto_pi_nhds.mpr
      intro x
      exact lp.hasSum_single (by norm_num) (ξ x)

theorem stronglyMeasurable_diagonal_apply (w : X → Weight)
    (hw : ∀ k : ℤ, StronglyMeasurable (fun x => w x k))
    (ξ : X → Hilbert) (hξ : StronglyMeasurable ξ) :
    StronglyMeasurable (fun x => diagonal (w x) (ξ x)) := by
  apply (stronglyMeasurable_iff_coordinates _).2
  intro k
  simpa only [diagonal_apply, Pi.mul_def] using
    (hw k).mul ((stronglyMeasurable_iff_coordinates ξ).1 hξ k)

theorem stronglyMeasurable_shift_apply (m : ℤ) (ξ : X → Hilbert)
    (hξ : StronglyMeasurable ξ) : StronglyMeasurable (fun x => shift m (ξ x)) :=
  (shift m).continuous.comp_stronglyMeasurable hξ

theorem stronglyMeasurable_operator_apply (w : X → Weight)
    (hw : ∀ k : ℤ, StronglyMeasurable (fun x => w x k))
    (ξ : X → Hilbert) (hξ : StronglyMeasurable ξ) :
    StronglyMeasurable (fun x => operator (w x) (ξ x)) :=
  stronglyMeasurable_shift_apply 1 _ (stronglyMeasurable_diagonal_apply w hw ξ hξ)

end Invariant233.WeightedShift

end

end OAI
