import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeRefreshNumbered
import OAI.Combinatorics.MatchingCount.Machines.TreePostRealization

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}
lemma index_min (a b : V) : Numbered.index (min a b)=min (Numbered.index a) (Numbered.index b) := by
  by_cases h : a≤b
  · rw [min_eq_left h,min_eq_left ((Numbered.index_le _ _).mpr h)]
  · rw [min_eq_right (le_of_not_ge h),min_eq_right ((Numbered.index_le _ _).mpr (le_of_not_ge h))]
lemma index_max (a b : V) : Numbered.index (max a b)=max (Numbered.index a) (Numbered.index b) := by
  by_cases h : a≤b
  · rw [max_eq_right h,max_eq_right ((Numbered.index_le _ _).mpr h)]
  · rw [max_eq_left (le_of_not_ge h),max_eq_left ((Numbered.index_le _ _).mpr (le_of_not_ge h))]
lemma sourceKey_numbering (p : ColoredPairing (numberedBags bags)) (i : Fin (Fintype.card V)) :
    sourceKey ((numberingEquiv bags p).edgeAt (orderedEnum V i))=key (p.edgeAt i) := by
  simp only [sourceKey,key,ColoredPairing.edgeAt,Sym2.inf_mk,Sym2.sup_mk]
  change ((Numbered.index (min (orderedEnum V i) (orderedEnum V (p.pair.mate ((orderedEnum V).symm (orderedEnum V i))))),
    Numbered.index (max (orderedEnum V i) (orderedEnum V (p.pair.mate ((orderedEnum V).symm (orderedEnum V i)))))),
      Numbered.index (orderedEnum L (p.color ((orderedEnum V).symm (orderedEnum V i))))) = _
  simp only [Equiv.symm_apply_apply]
  simp only [index_min,index_max,Numbered.index_orderedEnum]
  rfl
lemma rowKey_numbering (p : ColoredPairing (numberedBags bags)) (i : Fin (Fintype.card V)) :
    rowKey (resultRep p,i.val)=sourceKey ((numberingEquiv bags p).edgeAt (orderedEnum V i)) := by
  rw [rowKey_result,sourceKey_numbering]
lemma matching_numbering (p : ColoredPairing (numberedBags bags)) :
    matching (sourceCatalog bags,resultRep p)=
      Numbered.set (Computable.toMatching (numberingEquiv bags p)).val := by
  ext j
  simp only [matching,resultRep,List.length_ofFn,List.mem_toFinset,List.mem_map,List.mem_range]
  change (∃ i,i<Fintype.card V ∧ entryIndex ((sourceCatalog bags,resultRep p),i)=j) ↔ _
  simp only [Numbered.set,Finset.mem_map,Numbered.embedding,Function.Embedding.coeFn_mk,
    Computable.toMatching,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,hj⟩
    refine ⟨(numberingEquiv bags p).edgeAt (orderedEnum V ⟨i,hi⟩),⟨orderedEnum V ⟨i,hi⟩,rfl⟩,?_⟩
    rw [entryIndex,rowKey_numbering p ⟨i,hi⟩,sourceCatalog_index] at hj
    exact hj
  · rintro ⟨e,⟨i,rfl⟩,hj⟩
    refine ⟨Numbered.index i,((orderedEnum V).symm i).isLt,?_⟩
    change (sourceCatalog bags).idxOf (rowKey (resultRep p,((orderedEnum V).symm i).val))=j
    rw [rowKey_numbering p ((orderedEnum V).symm i),sourceCatalog_index,Equiv.apply_symm_apply]
    exact hj

lemma refresh_sampleMatching {k : ℕ} (bags : V→Finset L) (rank : L→ℕ) (parent : L→Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) (M : BagPM bags)
    (a : Bags) (ha : List.Forall₂ List.Perm a (orderedRep (numberedBags bags)))
    (bits : Fin (Fintype.card V)→Fin k→Bool) :
    refresh ((storedCatalog (a,List.range (Fintype.card L)),
      ((a,parentRep (numberedParent parent)),(Materialized.plan (numberedRank rank)).map Fin.val)),
      List.ofFn (fun i=>List.ofFn (bits i)))=
    Numbered.set (sampleMatching k bags rank parent hb hne hp M bits).val := by
  unfold refresh
  rw [storedCatalog_eq ha,←sourceCatalog_eq]
  rw [fastSample_represented (numberedBags bags) (numberedRank rank) (numberedParent parent)
    (numberedRanked bags rank parent hb) (numberedNonempty bags hne) (numberedDecreasing rank parent hp)
    (numbered_count_pos bags rank parent hb hne hp (Computable.pairingEquiv M)) a ha bits,matching_numbering]
  rfl

open TreePost Turing

theorem source_refresh_post : ∃ p : Polynomial ℕ,
    ∀ {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
      (bags : V→Finset L) (rank : L→ℕ) (parent : L→Option L)
      (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
      (hp : ∀ l p,parent l=some p → rank p<rank l) (M : BagPM bags)
      (a : Bags) (_ha : List.Forall₂ List.Perm a (orderedRep (numberedBags bags)))
      {k : ℕ} (bits : Fin (Fintype.card V)→Fin k→Bool) (t : ℕ),
      let x := ((storedCatalog (a,List.range (Fintype.card L)),
        ((a,parentRep (numberedParent parent)),(Materialized.plan (numberedRank rank)).map Fin.val)),
        List.ofFn (fun i=>List.ofFn (bits i)))
      p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine refreshRealizer.program) (packed x) coins).state=none ∧
      (run (machine refreshRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (Numbered.set (sampleMatching k bags rank parent hb hne hp M bits).val)) := by
  obtain ⟨p,hp⟩:=polynomial_compiles refreshRealizer polynomial_refresh
  refine ⟨p,fun {V L} _ _ _ _ bags rank parent hb hne hpar M a ha {k} bits t ht coins=>?_⟩
  have h:=hp ((storedCatalog (a,List.range (Fintype.card L)),
    ((a,parentRep (numberedParent parent)),(Materialized.plan (numberedRank rank)).map Fin.val)),
    List.ofFn (fun i=>List.ofFn (bits i))) t ht coins
  rwa [refresh_sampleMatching bags rank parent hb hne hpar M a ha bits] at h
end MatchingFPRAS.ExecutableRefresh

end OAI
