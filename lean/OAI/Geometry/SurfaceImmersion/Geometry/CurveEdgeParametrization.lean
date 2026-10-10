import OAI.Geometry.SurfaceImmersion.Geometry.CurveEdgeWitness
import OAI.Geometry.SurfaceImmersion.Atlas.LineChartEndpointObstruction

namespace OAI

/-! Retained edge witnesses give actual compact interval
parametrizations of their closures. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

def CurveEdgeWitness.param {V E : Set X} (w : CurveEdgeWitness V E) : Icc w.lo w.hi → X :=
  fun t => w.arc.map ⟨t.val,w.lower.trans t.property.1,t.property.2.trans w.upper⟩

lemma CurveEdgeWitness.param_closedEmbedding {V E : Set X} (w : CurveEdgeWitness V E) :
    IsClosedEmbedding w.param := by
  let j : Icc w.lo w.hi → Icc w.arc.left w.arc.right := fun t =>
    ⟨t.val,w.lower.trans t.property.1,t.property.2.trans w.upper⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hc : Continuous w.param := w.arc.embedding.continuous.comp hj
  apply hc.isClosedEmbedding
  intro s t hst
  have he := w.arc.embedding.injective hst
  exact Subtype.ext (congrArg (fun u : Icc w.arc.left w.arc.right => (u:ℝ)) he)

omit [T2Space X] in
lemma CurveEdgeWitness.param_range {V E : Set X} (w : CurveEdgeWitness V E) :
    range w.param = closure E := by
  conv_rhs => rw [w.piece_eq,w.arc.subarc_closure w.lower w.upper w.ordered]
  apply Subset.antisymm
  · rintro x ⟨t,rfl⟩
    exact ⟨⟨t.val,w.lower.trans t.property.1,t.property.2.trans w.upper⟩,t.property,rfl⟩
  · rintro x ⟨t,ht,rfl⟩
    exact ⟨⟨t.val,ht⟩,rfl⟩

lemma CurveEdgeWitness.frontier_not_interior_closure {V E : Set X} (w : CurveEdgeWitness V E)
    (d : OpenPartialHomeomorph X ℝ) {p : X} (hp : p ∈ d.source)
    (hb : p ∈ closure E \ E) : p ∉ interior (closure E) := by
  have hend : p = w.param ⟨w.lo,le_rfl,w.ordered.le⟩ ∨
      p = w.param ⟨w.hi,w.ordered.le,le_rfl⟩ := by
    rw [w.frontier_eq] at hb
    rcases hb with h | h
    · exact Or.inl h
    · exact Or.inr (mem_singleton_iff.mp h)
  rw [← w.param_range]
  exact compact_arc_endpoint_not_interior d w.ordered.le w.param w.param_closedEmbedding.isEmbedding hp hend

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
