import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleAtlas

namespace OAI

/-! A curve locally in the double locus has a continuous local lift to
its actual subtype, with an arbitrary fixed continuation outside the germ. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M]
variable {f : M → ProjectionTarget 3}

theorem local_double_curve_lift {C : ℝ → M × M} {x : ℝ}
    (hC : ContinuousAt C x) (p : surfaceDoublePairs f) (hp : p.val = C x)
    (hgood : ∀ᶠ t in 𝓝 x, C t ∈ surfaceDoublePairs f) :
    ∃ γ : ℝ → surfaceDoublePairs f, ContinuousAt γ x ∧ γ x = p ∧
      (fun t => (γ t).val) =ᶠ[𝓝 x] C := by
  classical
  let γ : ℝ → surfaceDoublePairs f := fun t =>
    if ht : C t ∈ surfaceDoublePairs f then ⟨C t,ht⟩ else p
  have he : (fun t => (γ t).val) =ᶠ[𝓝 x] C := by
    filter_upwards [hgood] with t ht
    dsimp only [γ]
    rw [dite_eq_left ht]
  have hcont : ContinuousAt (fun t => (γ t).val) x := hC.congr_of_eventuallyEq he
  have hγ : ContinuousAt γ x := (Topology.IsInducing.subtypeVal.continuousAt_iff).mpr hcont
  refine ⟨γ,hγ,?_,he⟩
  apply Subtype.ext
  exact he.eq_of_nhds.trans hp.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
