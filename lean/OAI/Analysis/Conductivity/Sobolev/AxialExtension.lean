import Mathlib
import OAI.Analysis.Conductivity.Flux.TorusBoxFlux

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def axialZeroExtension (d e : ℝ) (f : Coord3 → E) (x : Coord3) : E :=
  if d+e/2<x 0 then f x else 0

omit [NormedSpace ℝ E] in
lemma axialZeroExtension_eventually_self {d e : ℝ} {f : Coord3 → E} {x : Coord3}
    (hx : d+e/2<x 0) : axialZeroExtension d e f=ᶠ[𝓝 x] f := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hx] with y hy
  exact ite_eq_left hy

omit [NormedSpace ℝ E] in
lemma axialZeroExtension_eventually_zero {d e : ℝ} (he : 0<e) {f : Coord3 → E}
    (hf : ∀ x,x 0∈Icc d (d+e) → f x=0) {x : Coord3} (hx : x 0<d+e) :
    axialZeroExtension d e f=ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [(isOpen_lt (continuous_apply 0) continuous_const).mem_nhds hx] with y hy
  dsimp only [axialZeroExtension]
  split_ifs with hh
  · exact hf y ⟨by linarith only [he,hh],hy.le⟩
  · rfl

lemma axialZeroExtension_contDiff {n : WithTop ℕ∞} {d e : ℝ} (he : 0<e)
    {f : Coord3 → E} (hf : ContDiffOn ℝ n f {x | d<x 0})
    (hz : ∀ x,x 0∈Icc d (d+e) → f x=0) : ContDiff ℝ n (axialZeroExtension d e f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x 0<d+e
  · exact contDiffAt_const.congr_of_eventuallyEq (axialZeroExtension_eventually_zero he hz hx)
  · have hx' : d+e/2<x 0 := by linarith
    exact (hf.contDiffAt ((axial_halfspace_open d).mem_nhds (show d<x 0 by linarith))).congr_of_eventuallyEq
      (axialZeroExtension_eventually_self hx')

omit [NormedSpace ℝ E] in
lemma axialZeroExtension_periodic {T d e : ℝ} {f : Coord3 → E}
    (hf : AngularPeriodic T f) : AngularPeriodic T (axialZeroExtension d e f) := by
  intro n x
  change (if d+e/2<x 0+0 then f (x+angularShift T n) else 0)=_
  rw [add_zero,hf n x]
  rfl

lemma axialZeroExtension_divergence {d e : ℝ} (he : 0<e) {F : Coord3 → Coord3}
    (hz : ∀ x,x 0∈Icc d (d+e) → F x=0)
    (hd : ∀ x,d<x 0 → coordinateDivergence F x=0) (x : Coord3) :
    coordinateDivergence (axialZeroExtension d e F) x=0 := by
  by_cases hx : x 0<d+e
  · rw [coordinateDivergence_congr_nhds (axialZeroExtension_eventually_zero he hz hx)]
    simp [coordinateDivergence]
  · rw [coordinateDivergence_congr_nhds (axialZeroExtension_eventually_self (by linarith : d+e/2<x 0))]
    exact hd x (by linarith)

end ScalarConductivity

end
end

end OAI
