import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Cutoff
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CutoffObservation
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Observation
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivatives

namespace OAI

noncomputable section
namespace VelocityDetection.Cutoff
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators

theorem cutoff_zero_on_upper {R : ℝ} (hR : 0 < R) {c : Coord 2}
    (hc : c 1 ≤ -R) {X : Coord 2} (hX : X ∈ Observation.upperHalfPlane) :
    cutoff R (X - c) = 0 := by
  apply cutoff_zero hR
  refine ⟨1, ?_⟩
  change R ≤ |X 1 - c 1|
  have hX' : 0 < X 1 := hX
  exact le_trans (by linarith) (le_abs_self _)

theorem cutoff_zero_off_upper {R : ℝ} (hR : 0 < R) {c : Coord 2}
    (hc : R ≤ c 1) {X : Coord 2} (hX : X ∉ Observation.upperHalfPlane) :
    cutoff R (X - c) = 0 := by
  apply cutoff_zero hR
  refine ⟨1, ?_⟩
  change R ≤ |X 1 - c 1|
  have hX' : X 1 ≤ 0 := not_lt.mp hX
  exact le_trans (by linarith) (neg_le_abs _)

theorem upper_mass_small {R δ : ℝ} (hR : 0 < R) {c : Coord 2}
    {ρ : Coord 2 → ℝ} (hρ : Integrable ρ) (hρ0 : ∀ X, 0 ≤ ρ X)
    (hc : c 1 ≤ -R) (hδ : δ < 1 / 24)
    (hretained : (∫ X, ρ X) - (∫ X, cutoff R (X - c) * ρ X) ≤ δ) :
    (∫ X in Observation.upperHalfPlane, ρ X) < (1 / 4 : ℝ) := by
  apply CutoffObservation.negative_margin
    (isOpen_lt continuous_const (continuous_apply 1) |>.measurableSet) hρ hρ0
    ((contDiff_cutoff R).continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    (fun X => (cutoff_mem_Icc R (X - c)).1) (fun X => (cutoff_mem_Icc R (X - c)).2)
    (fun X hX => cutoff_zero_on_upper hR hc hX) hδ
  change (∫ X, ρ X) - δ ≤ ∫ X, cutoff R (X - c) * ρ X
  linarith

theorem upper_mass_large {R δ : ℝ} (hR : 0 < R) {c : Coord 2}
    {ρ : Coord 2 → ℝ} (hρ : Integrable ρ) (hρ0 : ∀ X, 0 ≤ ρ X)
    (hc : R ≤ c 1) (hδ : δ < 1 / 24) (hmass : (∫ X, ρ X) = 1)
    (hretained : (∫ X, ρ X) - (∫ X, cutoff R (X - c) * ρ X) ≤ δ) :
    (3 / 4 : ℝ) < ∫ X in Observation.upperHalfPlane, ρ X := by
  apply CutoffObservation.positive_margin
    (isOpen_lt continuous_const (continuous_apply 1) |>.measurableSet) hρ hρ0
    ((contDiff_cutoff R).continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    (fun X => (cutoff_mem_Icc R (X - c)).1) (fun X => (cutoff_mem_Icc R (X - c)).2)
    (fun X hX => cutoff_zero_off_upper hR hc hX) hmass hδ
  change (∫ X, ρ X) - δ ≤ ∫ X, cutoff R (X - c) * ρ X
  linarith

end VelocityDetection.Cutoff
end

end OAI
