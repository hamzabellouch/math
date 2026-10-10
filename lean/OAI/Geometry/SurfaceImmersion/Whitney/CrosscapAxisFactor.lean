import OAI.Geometry.SurfaceImmersion.Geometry.AxisNormalizedDefect

namespace OAI

/-! Applying the axis normalization to the actual crosscap strip. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.normal_defect_axis_factor (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    ∃ (a : Fin 3 → ℝ) (d : ℝ → Base) (W : Set ℝ), ContDiff ℝ ∞ d ∧ IsOpen W ∧
      Icc A.arc.start A.arc.finish ⊆ W ∧ (∀ t ∈ W, d t ≠ 0) ∧
      ∀ t ∈ W, axisNormalizedDefect d (normalDefect S.model a) (crosscapAxis t) =
        ![(t-A.arc.start)*(t-A.arc.finish),0] := by
  obtain ⟨a,δ,U,hδ,hU,_hUD,hrect,hN,hz,hDp,hDq⟩ := S.nondegenerate_normal_defect hf
  have haxis : ∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ U := by
    intro t ht
    rw [crosscapAxis_apply]
    apply hrect 0 (by constructor <;> linarith) t
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨d,W,hd,hW,hKW,hn,he⟩ := two_zero_axis_factor hU hN A.arc.start_lt_finish
    haxis (by simpa only [crosscapAxis_apply] using hz)
    (by simpa only [crosscapAxis_apply] using hDp)
    (by simpa only [crosscapAxis_apply] using hDq)
  let V := W ∩ {t | d t ≠ 0}
  have hV : IsOpen V := hW.inter (isOpen_ne.preimage hd.continuous)
  refine ⟨a,d,V,hd,hV,?_,fun _ ht => ht.2,?_⟩
  · exact fun t ht => ⟨hKW ht,hn t ht⟩
  · intro t ht
    exact axisNormalizedDefect_axis ht.2 (he t ht.1)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
