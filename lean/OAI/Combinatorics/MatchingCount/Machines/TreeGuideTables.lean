import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeNumberedSets
import OAI.Combinatorics.MatchingCount.Algorithm.TreeTierWeights

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

def slotUniverse (x : TierData) : Finset ℕ := (slots x).toFinset
def slotUniverseRealizer : Realizer slotUniverse := composition slotsRealizer (listFinset natEqual leNat)
lemma polynomial_slotUniverse : PolynomialTime slotUniverseRealizer :=
  polynomial_composition polynomial_slots (polynomial_listFinset polynomial_natEqual polynomial_leNat)

def guideTest (x : (TierData×ℕ)×ℕ) : Bool :=
  decide (x.1.2/x.1.1.2.1.length<x.1.1.1.2.length ∧
    x.2/x.1.1.2.1.length=x.1.2/x.1.1.2.1.length+1)
def guideTestRealizer : Realizer guideTest := by
  let q : Realizer (fun x : (TierData×ℕ)×ℕ=>x.1.1.2.1.length) := composition first.fst.snd.fst listLength
  let r : Realizer (fun x : (TierData×ℕ)×ℕ=>x.1.2/x.1.1.2.1.length) := composition (pair first.snd q) quotient
  exact (composition (pair (composition (pair r (composition first.fst.fst.snd listLength)) less)
    (composition (pair (composition (pair second q) quotient) (composition r successor)) natEqual)) boolAnd).congr
    (by intro x; simp [guideTest])
lemma polynomial_guideTest : PolynomialTime guideTestRealizer := by
  unfold guideTestRealizer Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have := polynomial_quotient
  have := polynomial_successor
  tree_cost

def guideSet (x : TierData×ℕ) : Finset ℕ := (slotUniverse x.1).filter (fun j=>guideTest (x,j))
def guideSetRealizer : Realizer guideSet := composition (pair identity (composition first slotUniverseRealizer))
  (finsetFilterWith guideTestRealizer)
lemma polynomial_guideSet : PolynomialTime guideSetRealizer := by
  unfold guideSetRealizer
  exact polynomial_composition (TreeTyped.polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_slotUniverse)) (polynomial_finsetFilterWith polynomial_guideTest)

def guideRows (x : TierData) : List (List ℕ) := (slots x).map (fun i=>(guideSet (x,i)).sort (·≤·))
def guideRowsRealizer : Realizer guideRows := composition (pair identity slotsRealizer)
  (mapWith (composition guideSetRealizer finsetList))
lemma polynomial_guideRows : PolynomialTime guideRowsRealizer := by
  unfold guideRowsRealizer
  exact polynomial_composition (TreeTyped.polynomial_pair polynomial_identity polynomial_slots)
    (polynomial_mapWith (polynomial_composition polynomial_guideSet polynomial_finsetList))

lemma slotUniverse_source (n : ℕ) (ft fq : List Bool) (ws : List Fraction) :
    slotUniverse ((n,ft),(fq,ws))=Numbered.set (Finset.univ : Finset (Slot ft.length fq.length)) := by
  ext j
  simp only [slotUniverse,slots,slotCount,List.toFinset_range,Finset.mem_range,Numbered.set,Finset.mem_map,
    Finset.mem_univ,true_and,Numbered.embedding]
  constructor
  · intro h
    let z : Fin (Fintype.card (Slot ft.length fq.length)) := ⟨j,by simpa only [slot_card] using h⟩
    exact ⟨UnitRefresh.orderedEnum _ z,index_enum z⟩
  · rintro ⟨z,rfl⟩
    change index z<(ft.length+1)*fq.length
    have h := ((UnitRefresh.orderedEnum (Slot ft.length fq.length)).symm z).isLt
    simpa only [index,slot_card] using h

lemma mem_guides_rank {T q : ℕ} (i j : Slot T q) :
    j∈guides i ↔ rank i<T ∧ rank j=rank i+1 := by
  unfold guides
  split_ifs with h
  · simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨h,rfl⟩
    · rintro ⟨_,he⟩
      refine ⟨(ofLex j).2,?_⟩
      apply ofLex.injective
      apply Prod.ext
      · exact Fin.ext he.symm
      · rfl
  · simp [h]

lemma guideSet_source (n : ℕ) (ft fq : List Bool) (ws : List Fraction) (i : Slot ft.length fq.length) :
    guideSet (((n,ft),(fq,ws)),index i)=Numbered.set (guides i) := by
  rw [guideSet,slotUniverse_source]
  ext j
  simp only [Finset.mem_filter,Numbered.set,Finset.mem_map,Finset.mem_univ,true_and,Numbered.embedding]
  constructor
  · rintro ⟨⟨z,rfl⟩,h⟩
    refine ⟨z,?_,rfl⟩
    rw [mem_guides_rank]
    simpa [guideTest,slot_index_div] using h
  · rintro ⟨z,h,rfl⟩
    refine ⟨⟨z,rfl⟩,?_⟩
    simpa [guideTest,slot_index_div] using (mem_guides_rank i z).mp h

lemma guideRows_source (n : ℕ) (ft fq : List Bool) (ws : List Fraction) :
    guideRows ((n,ft),(fq,ws))=List.ofFn
      (fun i : Fin (Fintype.card (Slot ft.length fq.length))=>
        (Numbered.set (guides (UnitRefresh.orderedEnum _ i))).sort (·≤·)) := by
  rw [guideRows,slots,slotCount,range_slot_indices,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact congrArg (fun values=>values.sort (·≤·))
    (guideSet_source n ft fq ws (UnitRefresh.orderedEnum _ i))

end MatchingFPRAS.NumericLadder

end OAI
