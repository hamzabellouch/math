import OAI.Combinatorics.ContingencyTables.Transport.FiniteGraphCutSemantics
import OAI.Combinatorics.ContingencyTables.Rooted.RootedIntegerEvaluation

namespace OAI

/-! # Exact canonical cut flags in the row-then-column vertex encoding -/

namespace ContingencyTables.RootedCutReindex

open SimpleGraph RootedCompletion
open scoped Classical

variable {V W : Type*}

lemma delete_comap (G : SimpleGraph V) (e : W ≃ V) (u v : W) :
    (G.comap e).deleteEdges {s(u,v)}=(G.deleteEdges {s(e u,e v)}).comap e := by
  ext a b
  simp only [SimpleGraph.deleteEdges_adj,SimpleGraph.comap_adj,Set.mem_singleton_iff,
    Sym2.eq_iff,e.injective.eq_iff]

lemma reachable_comap (G : SimpleGraph V) (e : W ≃ V) (u v : W) :
    (G.comap e).Reachable u v ↔ G.Reachable (e u) (e v) := by
  constructor
  · intro h
    exact h.map (SimpleGraph.Iso.comap e G).toHom
  · intro h
    have hh := h.map (SimpleGraph.Iso.comap e G).symm.toHom
    change (G.comap e).Reachable (e.symm (e u)) (e.symm (e v)) at hh
    simpa only [Equiv.symm_apply_apply] using hh

lemma away_comap (G : SimpleGraph V) (e : W ≃ V) (u v root : W) :
    e (RootedCut.away (G.comap e) u v root)=RootedCut.away G (e u) (e v) (e root) := by
  unfold RootedCut.away
  rw [delete_comap,reachable_comap]
  split_ifs <;> rfl

lemma cut_comap (G : SimpleGraph V) (e : W ≃ V) (u v root a : W) :
    RootedCut.cut (G.comap e) u v root a=RootedCut.cut G (e u) (e v) (e root) (e a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [RootedCut.cut,MaximumForest.side,decide_eq_true_eq]
  rw [delete_comap,reachable_comap,away_comap]

/-- The Boolean program computes exactly the selected-root tree cut
used in the affine coefficient, with the concrete row/column order. -/
lemma canonicalCut_treeCut {m n : ℕ} (T : SimpleGraph (Fin m⊕Fin n))
    [DecidableRel T.Adj] (t : GraphCompletionCounts.TreeCell T) (a : Fin m⊕Fin n) :
    FiniteGraphCutProgram.canonicalCutCode
      ((FiniteGraphRootProgram.graphCode (T.comap finSumFinEquiv.symm),
        ((finSumFinEquiv (m := m) (n := n) (.inl t.val.1)).val,(finSumFinEquiv (m := m) (n := n) (.inr t.val.2)).val)),
        (finSumFinEquiv a).val)=RootedCut.treeCut T (rowColumn T) t a := by
  rw [FiniteGraphCutProgram.canonicalCutCode_graph]
  rw [cut_comap]
  simp only [RootedCut.treeCut,rowColumn_root,Equiv.symm_apply_apply]

end ContingencyTables.RootedCutReindex

end OAI
