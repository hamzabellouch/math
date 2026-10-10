import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeSamplerRows
import OAI.Combinatorics.MatchingCount.Machines.TreeIndex
import OAI.Combinatorics.MatchingCount.Machines.TreeNumberedSets

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Polynomial

abbrev Key := (ℕ×ℕ)×ℕ

def ordered (x : ℕ×ℕ) : ℕ×ℕ := if x.1<x.2 then x else (x.2,x.1)
def orderedRealizer : Realizer ordered := (choose less identity (pair second first)).congr (by intro x; simp [ordered])
lemma polynomial_ordered : PolynomialTime orderedRealizer := by
  unfold orderedRealizer; apply polynomial_congr; tree_cost
lemma ordered_eq (a b : ℕ) : ordered (a,b)=(min a b,max a b) := by
  by_cases h : a<b
  · simp [ordered,h,min_eq_left h.le,max_eq_right h.le]
  · simp [ordered,h,min_eq_right (le_of_not_gt h),max_eq_left (le_of_not_gt h)]

def rowKey (x : Result×ℕ) : Key :=
  (ordered (x.2,(x.1.getD x.2 (0,0)).1),(x.1.getD x.2 (0,0)).2)
def rowKeyRealizer : Realizer rowKey := (pair
  (composition (pair second (composition (getDFast (0,0)) first)) orderedRealizer)
  (composition (getDFast (0,0)) second)).congr (fun _=>rfl)
lemma polynomial_rowKey : PolynomialTime rowKeyRealizer := by
  unfold rowKeyRealizer; apply polynomial_congr
  have := polynomial_getDFast ((0,0) : ℕ×ℕ)
  have := polynomial_ordered
  tree_cost

def entryIndex (x : (List Key×Result)×ℕ) : ℕ := x.1.1.idxOf (rowKey (x.1.2,x.2))
def entryIndexRealizer : Realizer entryIndex := composition
  (pair (composition (pair first.snd second) rowKeyRealizer) first.fst)
  (indexOf (pairEqual (pairEqual natEqual natEqual) natEqual))
lemma polynomial_entryIndex : PolynomialTime entryIndexRealizer := by
  unfold entryIndexRealizer entryIndex
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_rowKey
  have := polynomial_indexOf (polynomial_pairEqual (polynomial_pairEqual polynomial_natEqual polynomial_natEqual) polynomial_natEqual)
  tree_cost

def matching (x : List Key×Result) : Finset ℕ :=
  ((List.range x.2.length).map (fun i=>entryIndex (x,i))).toFinset
def matchingRealizer : Realizer matching := (composition
  (composition (pair identity (composition (composition second listLength) range))
    (mapWith entryIndexRealizer)) (listFinset natEqual leNat)).congr (fun _=>rfl)
lemma polynomial_matching : PolynomialTime matchingRealizer := by
  have hr : PolynomialTime (composition (composition (second (A:=List Key) (B:=Result)) listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_listLength) X
    intro x
    simpa only [eval_X,Function.comp_apply] using (list_length_le_weight x.2).trans (weight_snd x)
  unfold matchingRealizer; apply polynomial_congr
  have := polynomial_entryIndex
  have := polynomial_listFinset polynomial_natEqual polynomial_leNat
  tree_cost

section Source
open Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {n m : ℕ} {bags : Fin n→Finset (Fin m)}
def key (e : BagEdge bags) : Key := ((e.val.val.1.inf.val,e.val.val.1.sup.val),e.val.val.2.val)
def catalog (bags : Fin n→Finset (Fin m)) : List Key :=
  List.ofFn (fun i=>key (orderedEnum (BagEdge bags) i))
lemma key_injective : Function.Injective (key (bags:=bags)) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Sym2.sortEquiv.injective
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z=>z.1.1) h)
    · exact Fin.ext (congrArg (fun z=>z.1.2) h)
  · exact Fin.ext (congrArg Prod.snd h)
lemma catalog_index (e : BagEdge bags) : (catalog bags).idxOf (key e)=Numbered.index e := by
  let i := (orderedEnum (BagEdge bags)).symm e
  have hn : (catalog bags).Nodup := List.nodup_ofFn.mpr ((key_injective (bags:=bags)).comp (orderedEnum (BagEdge bags)).injective)
  have hi : i.val<(catalog bags).length := by simp only [catalog,List.length_ofFn]; exact i.isLt
  dsimp only [catalog] at hi hn
  have h:=@List.Nodup.idxOf_getElem Key (inferInstance : BEq Key) inferInstance _ hn i.val hi
  have hget : (List.ofFn (fun j=>key (orderedEnum (BagEdge bags) j)))[i.val]'hi=key e := by
    rw [List.getElem_ofFn]
    simp only [Fin.eta,i,Equiv.apply_symm_apply]
  rw [hget] at h
  exact h
lemma rowKey_result (p : ColoredPairing bags) (i : Fin n) :
    rowKey (resultRep p,i.val)=key (p.edgeAt i) := by
  unfold rowKey
  rw [resultRep_getD,ordered_eq]
  rfl
lemma matching_result (p : ColoredPairing bags) :
    matching (catalog bags,resultRep p)=Numbered.set (Computable.toMatching p).val := by
  ext j
  simp only [matching,resultRep,List.length_ofFn,List.mem_toFinset,List.mem_map,List.mem_range]
  change (∃ i, i<n ∧ entryIndex ((catalog bags,resultRep p),i)=j) ↔ _
  simp only [Numbered.set,Finset.mem_map,Numbered.embedding,Function.Embedding.coeFn_mk,
    Computable.toMatching,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,hj⟩
    refine ⟨p.edgeAt ⟨i,hi⟩,⟨⟨i,hi⟩,rfl⟩,?_⟩
    rw [entryIndex,rowKey_result p ⟨i,hi⟩,catalog_index] at hj
    exact hj
  · rintro ⟨e,⟨i,rfl⟩,hj⟩
    refine ⟨i.val,i.isLt,?_⟩
    rw [entryIndex,rowKey_result,catalog_index]
    exact hj
end Source

abbrev Input := (List Key×CountInput)×Bits
def refresh (x : Input) : Finset ℕ := matching (x.1.1,fastSample (x.1.2,x.2))
def refreshRealizer : Realizer refresh := composition
  (pair first.fst (composition (pair first.snd second) fastSampleRealizer)) matchingRealizer
lemma polynomial_refresh : PolynomialTime refreshRealizer := by
  unfold refreshRealizer refresh
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_fastSample
  have := polynomial_matching
  tree_cost

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
lemma refresh_source {n m k : ℕ} (bags : Fin n→Finset (Fin m))
    (rank : Fin m→ℕ) (parent : Fin m→Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p→ rank p<rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))
    (a : Bags) (ha : List.Forall₂ List.Perm a (orderedRep bags)) (bits : Fin n→Fin k→Bool) :
    refresh ((catalog bags,((a,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val)),
      List.ofFn (fun i=>List.ofFn (bits i)))=
    Numbered.set (UnitRefresh.Computable.toMatching
      (UnitRefresh.Materialized.sampleUnit k n bags rank parent hb hne hp hz bits)).val := by
  unfold refresh
  rw [fastSample_represented bags rank parent hb hne hp hz a ha bits,matching_result]
end MatchingFPRAS.ExecutableRefresh

end OAI
