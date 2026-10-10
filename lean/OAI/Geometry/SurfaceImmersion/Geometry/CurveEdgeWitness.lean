import OAI.Geometry.SurfaceImmersion.Geometry.SubarcClosure

namespace OAI

/-! Each finite curve edge retains its actual compact interval
parametrization, two distinct endpoints, and exact frontier. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

structure CurveEdgeWitness (V E : Set X) where
  arc : CompactCurveArc X
  lo : ℝ
  hi : ℝ
  lower : arc.left ≤ lo
  upper : hi ≤ arc.right
  ordered : lo < hi
  piece_eq : E = arc.openSubarc lo hi
  left_mem : arc.map ⟨lo,lower,ordered.le.trans upper⟩ ∈ V
  right_mem : arc.map ⟨hi,lower.trans ordered.le,upper⟩ ∈ V

def CurveEdgeWitness.leftPoint {V E : Set X} (w : CurveEdgeWitness V E) : X :=
  w.arc.map ⟨w.lo,w.lower,w.ordered.le.trans w.upper⟩

def CurveEdgeWitness.rightPoint {V E : Set X} (w : CurveEdgeWitness V E) : X :=
  w.arc.map ⟨w.hi,w.lower.trans w.ordered.le,w.upper⟩

lemma CurveEdgeWitness.endpoints_ne {V E : Set X} (w : CurveEdgeWitness V E) :
    w.leftPoint ≠ w.rightPoint := by
  intro he
  have ht := w.arc.embedding.injective he
  exact w.ordered.ne (congrArg Subtype.val ht)

variable [T2Space X]
lemma CurveEdgeWitness.frontier_eq {V E : Set X} (w : CurveEdgeWitness V E) :
    closure E \ E = {w.leftPoint,w.rightPoint} := by
  conv_lhs => rw [w.piece_eq]
  exact w.arc.subarc_boundary_eq w.lower w.upper w.ordered

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
