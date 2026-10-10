import OAI.Combinatorics.Crossing.PolygonComposition
import OAI.Combinatorics.Crossing.PolygonalChainOperations
import OAI.Combinatorics.Crossing.ClosedPolygonIntersection

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b c : Plane}

def reverse (P : PolygonalChain O a b) : PolygonalChain O b a where
  pieces := P.pieces
  vertices := reversedSequence P.vertices P.pieces
  first := by simpa only [reversedSequence,Nat.sub_zero] using P.last
  last := by simpa only [reversedSequence,Nat.sub_self] using P.first
  start_mem := P.path_range_subset ⟨1,P.path.target⟩
  inside := by
    intro i hi
    have h₀ : P.pieces-i=P.pieces-1-i+1 := by omega
    have h₁ : P.pieces-(i+1)=P.pieces-1-i := by omega
    simp only [reversedSequence,h₀,h₁]
    rw [segment_symm]
    exact P.inside (P.pieces-1-i) (by omega)

theorem intersection_join_left (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (w : ℕ → Plane) (k : ℕ) :
    polygonIntersection (P.join Q).vertices w (P.join Q).pieces k=
      polygonIntersection P.vertices w P.pieces k+polygonIntersection Q.vertices w Q.pieces k :=
  polygonIntersection_join_left _ _ _ _ _ _ (P.last.trans Q.first.symm)

theorem intersection_join_right (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (w : ℕ → Plane) (k : ℕ) :
    polygonIntersection w (P.join Q).vertices k (P.join Q).pieces=
      polygonIntersection w P.vertices k P.pieces+polygonIntersection w Q.vertices k Q.pieces :=
  polygonIntersection_join_right _ _ _ _ _ _ (P.last.trans Q.first.symm)

theorem intersection_reverse_left (P : PolygonalChain O a b) (w : ℕ → Plane) (k : ℕ) :
    polygonIntersection P.reverse.vertices w P.reverse.pieces k = -polygonIntersection P.vertices w P.pieces k :=
  polygonIntersection_reverse_left _ _ _ _

theorem intersection_reverse_right (P : PolygonalChain O a b) (w : ℕ → Plane) (k : ℕ) :
    polygonIntersection w P.reverse.vertices k P.reverse.pieces = -polygonIntersection w P.vertices k P.pieces := by
  rw [polygonIntersection_swap,P.intersection_reverse_left,polygonIntersection_swap]
  ring

end Zarankiewicz.PolygonalChain

end

end OAI
