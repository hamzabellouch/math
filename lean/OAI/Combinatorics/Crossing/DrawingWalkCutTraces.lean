import OAI.Combinatorics.Crossing.DrawingEdgeWalkTrace

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem graphWalkPath_range_cases {V : Type*} {G : SimpleGraph V} (pos : V → Plane)
    {a b : V} (p : G.Walk a b) (x : Plane) (hx : x ∈ Set.range (graphWalkPath pos p)) :
    x=pos a ∨ ∃ i, i < p.length ∧ x ∈ segment ℝ (pos (p.getVert i)) (pos (p.getVert (i+1))) := by
  by_cases hp : p.length=0
  · change x ∈ Set.range (polygonalArcPath (fun i => pos (p.getVert i)) p.length) at hx
    rw [hp] at hx
    obtain ⟨t,ht⟩ := hx
    exact Or.inl (by simpa [polygonalArcPath,p.getVert_zero] using ht.symm)
  · exact Or.inr (polygonalArcPath_range_piece _ _ (by omega) x hx)

variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem drawingEdgeWalk_take_trace (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : BipartiteEdge m n) (k : Fin ((P e).pieces+1)) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P e).take k.val)) ⊆
      D.edge e '' Set.Icc (0 : unitInterval) ((P e).knot k) := by
  intro x hx
  rcases graphWalkPath_range_cases id ((drawingEdgeWalk P e).take k.val) x hx with he | ⟨i,hi,hxi⟩
  · exact ⟨0,⟨le_rfl,((P e).knot k).property.1⟩,(D.edge e).source.trans he.symm⟩
  · have hil : i < (P e).pieces := by
      rw [SimpleGraph.Walk.take_length,drawingEdgeWalk_length] at hi
      omega
    have hik : i+1 ≤ k.val := by
      rw [SimpleGraph.Walk.take_length,drawingEdgeWalk_length] at hi
      omega
    simp only [id_eq,SimpleGraph.Walk.take_getVert] at hxi
    rw [show min k.val i=i by omega,show min k.val (i+1)=i+1 by omega,
      drawingEdgeWalk_getVert P e i (by omega),drawingEdgeWalk_getVert P e (i+1) (by omega)] at hxi
    let j : Fin (P e).pieces := ⟨i,hil⟩
    have h0 : (P e).vertices i=D.edge e ((P e).knot j.castSucc) := (P e).vertices_at j.castSucc
    have h1 : (P e).vertices (i+1)=D.edge e ((P e).knot j.succ) := (P e).vertices_at j.succ
    rw [h0,h1] at hxi
    obtain ⟨t,ht⟩ := (P e).pieceTrace_parameter j x hxi
    have hbetween := intervalSegment_between ((P e).knot j.castSucc) ((P e).knot j.succ) t
      ((P e).increasing.monotone (by change i ≤ i+1; omega))
    exact ⟨intervalSegment ((P e).knot j.castSucc) ((P e).knot j.succ) t,
      ⟨(intervalSegment _ _ t).property.1,hbetween.2.trans ((P e).increasing.monotone hik)⟩,ht⟩

theorem drawingEdgeWalk_drop_trace (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : BipartiteEdge m n) (k : Fin ((P e).pieces+1)) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P e).drop k.val)) ⊆
      D.edge e '' Set.Icc ((P e).knot k) (1 : unitInterval) := by
  intro x hx
  rcases graphWalkPath_range_cases id ((drawingEdgeWalk P e).drop k.val) x hx with he | ⟨i,hi,hxi⟩
  · refine ⟨(P e).knot k,⟨le_rfl,((P e).knot k).property.2⟩,?_⟩
    have hh : (drawingEdgeWalk P e).getVert k.val=D.edge e ((P e).knot k) :=
      (drawingEdgeWalk_getVert P e k.val (by omega)).trans ((P e).vertices_at k)
    exact hh.symm.trans he.symm
  · have hil : k.val+i < (P e).pieces := by
      rw [SimpleGraph.Walk.drop_length,drawingEdgeWalk_length] at hi
      omega
    simp only [id_eq,SimpleGraph.Walk.drop_getVert] at hxi
    rw [drawingEdgeWalk_getVert P e (k.val+i) (by omega),
      drawingEdgeWalk_getVert P e (k.val+(i+1)) (by omega)] at hxi
    let j : Fin (P e).pieces := ⟨k.val+i,hil⟩
    have h0 : (P e).vertices (k.val+i)=D.edge e ((P e).knot j.castSucc) := (P e).vertices_at j.castSucc
    have h1 : (P e).vertices (k.val+(i+1))=D.edge e ((P e).knot j.succ) := by
      have hh : (P e).vertices (k.val+i+1)=D.edge e ((P e).knot j.succ) := (P e).vertices_at j.succ
      simpa only [Nat.add_assoc] using hh
    rw [h0,h1] at hxi
    obtain ⟨t,ht⟩ := (P e).pieceTrace_parameter j x hxi
    have hbetween := intervalSegment_between ((P e).knot j.castSucc) ((P e).knot j.succ) t
      ((P e).increasing.monotone (by change k.val+i ≤ k.val+i+1; omega))
    refine ⟨intervalSegment ((P e).knot j.castSucc) ((P e).knot j.succ) t,⟨?_,?_⟩,ht⟩
    · exact ((P e).increasing.monotone (show k ≤ j.castSucc by change k.val ≤ k.val+i; omega)).trans hbetween.1
    · exact (intervalSegment _ _ t).property.2

end Zarankiewicz

end

end OAI
