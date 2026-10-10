import OAI.Combinatorics.Crossing.AxisSegments
import Mathlib.Analysis.Convex.PathConnected

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def axisVertex (a : Fin m → ℝ) (b : Fin n → ℝ) : BipartiteVertex m n → Plane
  | .inl i => (0,a i)
  | .inr p => (b p,0)

theorem axisVertex_injective (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b) (ha : ∀ i, a i ≠ 0) :
    Function.Injective (axisVertex a b) := by
  rintro (i|p) (k|q) he
  · exact congrArg Sum.inl (hai (congrArg Prod.snd he))
  · exact False.elim (ha i (congrArg Prod.snd he))
  · exact False.elim (ha k (congrArg Prod.snd he).symm)
  · exact congrArg Sum.inr (hbi (congrArg Prod.fst he))

def axisContinuousDrawing (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) : ContinuousDrawing m n where
  vertex := axisVertex a b
  vertex_injective := axisVertex_injective a b hai hbi ha
  edge e := Path.segment (0,a e.1) (b e.2,0)
  edge_injective := by
    intro e t u he
    apply Subtype.ext
    apply axisSegmentPoint_injective (a e.1) (b e.2) (hb e.2)
    change AffineMap.lineMap (0,a e.1) (b e.2,0) t.val = AffineMap.lineMap (0,a e.1) (b e.2,0) u.val at he
    simpa only [AffineMap.lineMap_apply_module,axisSegmentPoint,segmentPoint] using he
  interior_avoids_vertices := by
    intro e t ht j he
    have hh := axisSegmentPoint_interior_off_axes (a e.1) (b e.2) t.val (ha e.1) (hb e.2) ⟨ht.1,ht.2⟩
    have hv : axisSegmentPoint (a e.1) (b e.2) t.val=axisVertex a b j := by
      change AffineMap.lineMap (0,a e.1) (b e.2,0) t.val = axisVertex a b j at he
      simpa only [AffineMap.lineMap_apply_module,axisSegmentPoint,segmentPoint] using he
    rcases j with i | p
    · exact hh.1 (congrArg Prod.fst hv)
    · exact hh.2 (congrArg Prod.snd hv)

theorem axisContinuousDrawing_interior (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ p, b p ≠ 0) (e : BipartiteEdge m n) :
    edgeInterior (axisContinuousDrawing a b hai hbi ha hb) e=openSegmentTrace (0,a e.1) (b e.2,0) := by
  ext x
  constructor
  · rintro ⟨t,ht,he⟩
    refine ⟨t.val,⟨ht.1,ht.2⟩,?_⟩
    change AffineMap.lineMap (0,a e.1) (b e.2,0) t.val = x at he
    simpa only [AffineMap.lineMap_apply_module,segmentPoint] using he
  · rintro ⟨t,ht,he⟩
    refine ⟨⟨t,⟨ht.1.le,ht.2.le⟩⟩,⟨ht.1,ht.2⟩,?_⟩
    change AffineMap.lineMap (0,a e.1) (b e.2,0) t = x
    simpa only [AffineMap.lineMap_apply_module,segmentPoint] using he

end Zarankiewicz

end

end OAI
