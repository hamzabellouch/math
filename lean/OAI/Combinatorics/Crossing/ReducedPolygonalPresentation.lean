import OAI.Combinatorics.Crossing.SubdivisionSegments
import OAI.Combinatorics.Crossing.PolygonalArcInjective
import OAI.Combinatorics.Crossing.ArcRangeMinimality

namespace OAI

noncomputable section
namespace Zarankiewicz

def PolygonalParametrization.containedChain {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) : PolygonalChain (Set.range γ) a b where
  pieces := P.pieces
  vertices := P.vertices
  first := P.vertices_first
  last := P.vertices_last
  start_mem := ⟨0,γ.source⟩
  inside := by
    intro i hi
    let j : Fin P.pieces := ⟨i,hi⟩
    have h0 : P.vertices i=γ (P.knot j.castSucc) := P.vertices_at j.castSucc
    have h1 : P.vertices (i+1)=γ (P.knot j.succ) := P.vertices_at j.succ
    rw [h0,h1]
    exact P.pieceTrace_subset_range j

theorem PolygonalChain.pieces_pos_of_ne {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) (hab : a ≠ b) : 0 < P.pieces := by
  by_contra hh
  have hz : P.pieces=0 := by omega
  exact hab (P.first.symm.trans (hz ▸ P.last))

theorem exists_reduced_polygonalChain {a b : Plane} (γ : Path a b)
    (hinj : Function.Injective γ) (hpoly : HasFiniteAffineCover γ) :
    ∃ P : PolygonalChain (Set.range γ) a b,
      Set.range P.path=Set.range γ ∧ Function.Injective P.path ∧ 0 < P.pieces ∧
      (∀ i, i < P.pieces → P.vertices (i+1)-P.vertices i ≠ 0) ∧
      (∀ i, i+2 ≤ P.pieces →
        det2 (P.vertices (i+1)-P.vertices i) (P.vertices (i+2)-P.vertices (i+1)) ≠ 0) ∧
      (∀ Q : PolygonalChain (Set.range γ) a b, P.pieces ≤ Q.pieces) := by
  have hab : a ≠ b := by
    intro h
    exact zero_ne_one (hinj (γ.source.trans (h.trans γ.target.symm)))
  obtain ⟨Q⟩ := hpoly.nonempty_polygonalParametrization
  obtain ⟨P,hmin⟩ := exists_minimum_polygonalChain ⟨Q.containedChain⟩
  exact ⟨P,path_range_eq_of_subset γ P.path hinj P.path_range_subset,
    P.minimum_path_injective hab hmin,P.pieces_pos_of_ne hab,
    P.minimum_piece_ne_zero hmin,P.minimum_bend_det_ne_zero hmin,hmin⟩

end Zarankiewicz

end

end OAI
