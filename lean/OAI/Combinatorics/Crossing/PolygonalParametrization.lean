import OAI.Combinatorics.Crossing.IntervalSegments
import OAI.Combinatorics.Crossing.OffsetTrack
import OAI.Combinatorics.Crossing.SegmentContinuity

namespace OAI

noncomputable section
namespace Zarankiewicz

structure PolygonalParametrization {a b : Plane} (γ : Path a b) where
  pieces : ℕ
  knot : Fin (pieces+1) → unitInterval
  increasing : StrictMono knot
  first : knot 0=0
  last : knot (Fin.last pieces)=1
  affine : ∀ i : Fin pieces, ∀ t : unitInterval,
    γ (intervalSegment (knot i.castSucc) (knot i.succ) t) =
      segmentPoint (γ (knot i.castSucc)) (γ (knot i.succ)) t.val

namespace PolygonalParametrization
variable {a b : Plane} {γ : Path a b}

def vertices (P : PolygonalParametrization γ) (i : ℕ) : Plane :=
  γ (P.knot ⟨min i P.pieces,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)

theorem vertices_at (P : PolygonalParametrization γ) (i : Fin (P.pieces+1)) :
    P.vertices i.val=γ (P.knot i) := by
  unfold vertices
  congr 2
  apply Fin.ext
  exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)

theorem vertices_first (P : PolygonalParametrization γ) : P.vertices 0=a := by
  have he := P.vertices_at (0 : Fin (P.pieces+1))
  rw [P.first] at he
  simpa using he.trans γ.source

theorem vertices_last (P : PolygonalParametrization γ) : P.vertices P.pieces=b := by
  have he := P.vertices_at (Fin.last P.pieces)
  rw [P.last] at he
  simpa using he.trans γ.target

theorem segment_formula (P : PolygonalParametrization γ) (i : Fin P.pieces) (t : unitInterval) :
    γ (intervalSegment (P.knot i.castSucc) (P.knot i.succ) t)=
      segmentPoint (P.vertices i.val) (P.vertices (i.val+1)) t.val := by
  have he := P.affine i t
  rw [← P.vertices_at i.castSucc,← P.vertices_at i.succ] at he
  simpa using he

theorem direction_ne_zero (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i : ℕ) (hi : i < P.pieces) : trackDirection P.vertices i ≠ 0 := by
  let j : Fin P.pieces := ⟨i,hi⟩
  intro hzero
  have he : P.vertices (i+1)=P.vertices i := sub_eq_zero.mp hzero
  have h₀ : P.vertices i=γ (P.knot j.castSucc) := by simpa [j] using P.vertices_at j.castSucc
  have h₁ : P.vertices (i+1)=γ (P.knot j.succ) := by simpa [j] using P.vertices_at j.succ
  rw [h₁,h₀] at he
  have hlt := P.increasing (show j.castSucc < j.succ by change i < i+1; omega)
  exact hlt.ne (hγ he).symm

theorem segments_disjoint_before (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i j : Fin P.pieces) (hij : i.val+1 < j.val) :
    ¬ ClosedSegmentsMeet (P.vertices i.val) (P.vertices (i.val+1))
      (P.vertices j.val) (P.vertices (j.val+1)) := by
  rintro ⟨s,hs,t,ht,he⟩
  let s' : unitInterval := ⟨s,hs⟩
  let t' : unitInterval := ⟨t,ht⟩
  have hparams := hγ ((P.segment_formula i s').trans (he.trans (P.segment_formula j t').symm))
  have hi := intervalSegment_between (P.knot i.castSucc) (P.knot i.succ) s'
    (P.increasing.monotone (show i.castSucc ≤ i.succ by change i.val ≤ i.val+1; omega))
  have hj := intervalSegment_between (P.knot j.castSucc) (P.knot j.succ) t'
    (P.increasing.monotone (show j.castSucc ≤ j.succ by change j.val ≤ j.val+1; omega))
  have hmid := P.increasing (show i.succ < j.castSucc from hij)
  have hlt := hi.2.trans_lt (hmid.trans_le hj.1)
  exact hlt.ne hparams

theorem nonadjacent_segments_disjoint (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i j : Fin P.pieces) (hij : i.val+1 < j.val ∨ j.val+1 < i.val) :
    ¬ ClosedSegmentsMeet (P.vertices i.val) (P.vertices (i.val+1))
      (P.vertices j.val) (P.vertices (j.val+1)) := by
  rcases hij with hij | hji
  · exact P.segments_disjoint_before hγ i j hij
  · rintro ⟨s,hs,t,ht,he⟩
    exact P.segments_disjoint_before hγ j i hji ⟨t,ht,s,hs,he.symm⟩

end PolygonalParametrization
end Zarankiewicz

end

end OAI
