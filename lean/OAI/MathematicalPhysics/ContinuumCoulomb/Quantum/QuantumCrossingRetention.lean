import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSelectCorrectness

namespace OAI

/-! Exact retained-edge semantics of the finite crossing scan. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumCrossingListBlock
open scoped BigOperators Classical

theorem pairs_ofFn_mem {r : ℕ} (ss : Fin r → Sites) (p : QuantumRouteCode.Pair) :
    p ∈ pairs (List.ofFn ss) ↔ ∃ i a, terminalPair a (ss i)=p := by
  rw [pairs,List.map_ofFn]
  constructor
  · intro h
    obtain ⟨xs,hxs,hp⟩ := List.mem_flatten.mp h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hxs
    rcases List.mem_cons.mp hp with hp | hp
    · exact ⟨i,0,hp.symm⟩
    · exact ⟨i,1,(List.mem_singleton.mp hp).symm⟩
  · rintro ⟨i,a,rfl⟩
    apply List.mem_flatten.mpr
    refine ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    fin_cases a <;> simp

theorem keep_selected {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
    (e : G.Edge) :
    keep (pairs (List.ofFn (encodedSites S.site)),
      ((G.left e).val,(G.right e).val,G.weight e))=decide (S.tag e=none) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  change (!(pairs (List.ofFn (encodedSites S.site))).any
    (fun p => hits (((G.left e).val,(G.right e).val,G.weight e),p)))=true ↔ _
  rw [Bool.not_eq_true_eq_eq_false,List.any_eq_false]
  constructor
  · intro h
    cases ht : S.tag e with
    | none => rfl
    | some p =>
      have hm := (pairs_ofFn_mem (encodedSites S.site)
        (terminalPair p.2 (encodedSites S.site p.1))).mpr ⟨p.1,p.2,rfl⟩
      have hn := h _ hm
      rw [hits_selected S htag,ht] at hn
      exact (hn (by simp)).elim
  · intro ht p hp
    obtain ⟨i,a,rfl⟩ := (pairs_ofFn_mem (encodedSites S.site) p).mp hp
    rw [hits_selected S htag,ht]
    simp

private theorem filter_matrix (n : ℕ) (ps : List QuantumRouteCode.Pair)
    (es : List MediatorListProgram.Bond) :
    SourceBondLists.matrix n (retained (ps,es)) =
      (es.map (fun e => if keep (ps,e) then SourceBondLists.bondMatrix n e else 0)).sum := by
  unfold retained
  induction es with
  | nil => rfl
  | cons e es ih =>
    change (List.map (SourceBondLists.bondMatrix n)
      (List.filter (fun e => keep (ps,e)) (e::es))).sum = _
    change (List.map (SourceBondLists.bondMatrix n)
      (List.filter (fun e => keep (ps,e)) es)).sum = _ at ih
    cases h : keep (ps,e) <;> simp only [List.filter_cons,h,Bool.false_eq_true,
      ite_false,ite_true,List.map_cons,List.sum_cons,zero_add] <;> rw [ih]

theorem retained_matrix {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
    {m : ℕ} (labels : G.Edge ≃ Fin m) :
    SourceBondLists.matrix G.n
      (retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels))+
      (G.constant:ℂ) • 1 =
      qmaExchangeMatrix S.retained.left S.retained.right
        (fun e => (S.retained.weight e:ℝ)) S.retained.constant := by
  rw [filter_matrix]
  have hb (e : G.Edge) : SourceBondLists.bondMatrix G.n
      ((G.left e).val,(G.right e).val,G.weight e)=
        (G.weight e:ℂ) • sourceHeisenbergMatrix G.n (G.left e) (G.right e) := by
    rw [SourceBondLists.bondMatrix,dite_eq_left ⟨(G.left e).isLt,(G.right e).isLt⟩]
  simp only [QuantumListGraph.packed,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    keep_selected S htag,decide_eq_true_eq,hb]
  have hs := labels.symm.sum_comp (fun e => if S.tag e=none then
    (G.weight e:ℂ) • sourceHeisenbergMatrix G.n (G.left e) (G.right e) else 0)
  rw [hs,← qmaSumSubtypePredicate]
  rfl

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
