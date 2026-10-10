import OAI.Geometry.SurfaceImmersion.Geometry.CurveIncidenceGraph
import OAI.Geometry.SurfaceImmersion.Geometry.CurveEdgeParametrization
import Mathlib.Analysis.Convex.PathConnected

namespace OAI

/-! Convert paths in the finite incidence graph to actual continuous
paths in the compact double curve, using its retained interval maps. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

lemma CurveEdgeWitness.closure_pathConnected {V E : Set X} (w : CurveEdgeWitness V E) :
    IsPathConnected (closure E) := by
  let : PathConnectedSpace (Icc w.lo w.hi) := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc w.lo w.hi).isPathConnected ⟨w.lo,le_rfl,w.ordered.le⟩)
  rw [← w.param_range]
  exact isPathConnected_range w.param_closedEmbedding.continuous

def CurveEdgeWitness.middle {V E : Set X} (w : CurveEdgeWitness V E) : X :=
  w.param ⟨(w.lo+w.hi)/2,by constructor <;> linarith [w.ordered]⟩

omit [T2Space X] in
lemma CurveEdgeWitness.middle_mem {V E : Set X} (w : CurveEdgeWitness V E) : w.middle ∈ E := by
  apply (congrArg (fun S : Set X => w.middle ∈ S) w.piece_eq).mpr
  refine ⟨⟨(w.lo+w.hi)/2,by constructor <;> linarith [w.lower,w.upper,w.ordered]⟩,?_,rfl⟩
  constructor <;> linarith [w.ordered]

def curveNodePoint {V : Set X} {P : Finset (Set X)}
    (w : ∀ E : P, CurveEdgeWitness V E.val) : V ⊕ P → X
  | Sum.inl v => v.val
  | Sum.inr E => (w E).middle

lemma curve_incidence_adj_joined {V : Set X} {P : Finset (Set X)}
    (w : ∀ E : P, CurveEdgeWitness V E.val) {a b : V ⊕ P}
    (h : (curveIncidenceGraph V P).Adj a b) : Joined (curveNodePoint w a) (curveNodePoint w b) := by
  cases a with
  | inl v =>
    cases b with
    | inl u => exact False.elim h
    | inr E =>
      exact ((w E).closure_pathConnected.joinedIn _ h _
        (subset_closure (w E).middle_mem)).joined
  | inr E =>
    cases b with
    | inl v =>
      exact ((w E).closure_pathConnected.joinedIn _
        (subset_closure (w E).middle_mem) _ h).joined
    | inr F => exact False.elim h

lemma curve_incidence_walk_joined {V : Set X} {P : Finset (Set X)}
    (w : ∀ E : P, CurveEdgeWitness V E.val) {a b : V ⊕ P}
    (p : (curveIncidenceGraph V P).Walk a b) : Joined (curveNodePoint w a) (curveNodePoint w b) := by
  induction p with
  | nil => exact Joined.refl _
  | cons h p ih => exact (curve_incidence_adj_joined w h).trans ih

lemma curve_incidence_path_joined {V : Set X} {P : Finset (Set X)}
    (w : ∀ E : P, CurveEdgeWitness V E.val) (p q : V)
    (h : Nonempty ((curveIncidenceGraph V P).Path (Sum.inl p) (Sum.inl q))) :
    Joined p.val q.val := by
  obtain ⟨γ⟩ := h
  exact curve_incidence_walk_joined w γ.val

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
