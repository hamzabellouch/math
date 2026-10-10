import OAI.Combinatorics.Crossing.TruncatedSegmentTransversality
import OAI.Combinatorics.Crossing.ShortVertexRadius

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

structure VertexTruncation (D : ContinuousDrawing m n) where
  chain : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
    (D.vertex (.inl e.1)) (D.vertex (.inr e.2))
  minimal : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
    (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (chain e).pieces ≤ Q.pieces
  radius : ℝ
  radius_pos : 0 < radius
  short : ∀ e, 4*radius^2 < squaredLength ((chain e).vertices 1-(chain e).vertices 0) ∧
    4*radius^2 < squaredLength ((chain e).vertices (chain e).pieces-(chain e).vertices ((chain e).pieces-1))
  disks_disjoint : ∀ j k, j ≠ k →
    Disjoint (closedRoundDisk (D.vertex j) radius) (closedRoundDisk (D.vertex k) radius)
  piece_clearance : ∀ j e (i : Fin (chain e).pieces),
    ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(chain e).pieces)) →
    Disjoint (closedRoundDisk (D.vertex j) radius)
      (segment ℝ ((chain e).vertices i.val) ((chain e).vertices (i.val+1)))

theorem nonempty_vertexTruncation (D : ContinuousDrawing m n)
    (hpoly : ∀ e, HasFiniteAffineCover (D.edge e)) : Nonempty (VertexTruncation D) := by
  classical
  have hex (e : BipartiteEdge m n) := exists_reduced_polygonalChain (D.edge e) (D.edge_injective e) (hpoly e)
  choose P htrace hinj hpos hdir hbend hmin using hex
  obtain ⟨ρ,hρ,hdis,hclear⟩ := exists_vertex_piece_clearance D P hmin
  obtain ⟨r,hr,hrρ,hshort⟩ := exists_short_vertex_radius D P hmin ρ hρ
  refine ⟨⟨P,hmin,r,hr,hshort,?_,?_⟩⟩
  · intro j k hjk
    exact (hdis j k hjk).mono (closedRoundDisk_mono _ hr.le hrρ) (closedRoundDisk_mono _ hr.le hrρ)
  · intro j e i hi
    exact (hclear j e i hi).mono_left (closedRoundDisk_mono _ hr.le hrρ)

namespace VertexTruncation
variable {D : ContinuousDrawing m n} (V : VertexTruncation D)

def pieces (e : BipartiteEdge m n) : ℕ := (V.chain e).pieces

def vertices (e : BipartiteEdge m n) : ℕ → Plane := (V.chain e).truncatedVertices V.radius

def startPort (e : BipartiteEdge m n) : Plane := (V.chain e).startPort V.radius

def endPort (e : BipartiteEdge m n) : Plane := (V.chain e).endPort V.radius

theorem pieces_pos (e : BipartiteEdge m n) : 0 < V.pieces e := drawing_chain_pieces_pos D e (V.chain e)

theorem weak_short (e : BipartiteEdge m n) :
    V.radius^2 < squaredLength ((V.chain e).vertices 1-(V.chain e).vertices 0) ∧
    V.radius^2 < squaredLength ((V.chain e).vertices (V.chain e).pieces-(V.chain e).vertices ((V.chain e).pieces-1)) := by
  constructor <;> nlinarith [(V.short e).1,(V.short e).2,sq_nonneg V.radius]

def path (e : BipartiteEdge m n) : Path (V.startPort e) (V.endPort e) :=
  ((V.chain e).truncated (V.pieces_pos e) V.radius V.radius_pos (V.weak_short e).1 (V.weak_short e).2).path

theorem path_injective (e : BipartiteEdge m n) : Function.Injective (V.path e) :=
  (V.chain e).truncated_path_injective (V.minimal e) (V.pieces_pos e) V.radius V.radius_pos
    (V.short e).1 (V.short e).2

theorem path_hasFiniteAffineCover (e : BipartiteEdge m n) : HasFiniteAffineCover (V.path e) :=
  ((V.chain e).truncated (V.pieces_pos e) V.radius V.radius_pos (V.weak_short e).1 (V.weak_short e).2).hasFiniteAffineCover

theorem range_subset_edgeInterior (e : BipartiteEdge m n) : Set.range (V.path e) ⊆ edgeInterior D e :=
  truncated_range_subset_edgeInterior D V.chain V.minimal V.radius V.radius_pos V.short V.piece_clearance e

theorem direction_ne_zero (e : BipartiteEdge m n) (i : ℕ) (hi : i < V.pieces e) :
    trackDirection (V.vertices e) i ≠ 0 :=
  (V.chain e).truncated_direction_ne_zero (V.minimal e) V.radius V.radius_pos (V.short e).1 (V.short e).2 i hi

end VertexTruncation
end Zarankiewicz

end

end OAI
