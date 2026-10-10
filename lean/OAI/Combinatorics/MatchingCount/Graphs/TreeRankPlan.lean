import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Plan
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPCount
import OAI.Combinatorics.MatchingCount.Machines.TreeFastLookup
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostTactic

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped ExecutableDP Polynomial

def rankLe (a b : ℕ×ℕ) : Prop := b.1<a.1 ∨ (a.1=b.1 ∧ a.2≤b.2)
instance : DecidableRel rankLe := fun a b=>inferInstanceAs (Decidable (b.1<a.1 ∨ (a.1=b.1 ∧ a.2≤b.2)))
instance : IsTrans (ℕ×ℕ) rankLe := ⟨by intro a b c; simp only [rankLe]; omega⟩
instance : Std.Total rankLe := ⟨by intro a b; simp only [rankLe]; omega⟩
instance : Std.Antisymm rankLe := ⟨by intro a b hab hba; simp only [rankLe] at *; apply Prod.ext <;> omega⟩

def rankLeRealizer : Realizer (fun x : (ℕ×ℕ)×(ℕ×ℕ)=>decide (rankLe x.1 x.2)) :=
  (composition (pair (composition (pair second.fst first.fst) less)
    (composition (pair (composition (pair first.fst second.fst) natEqual)
      (composition (pair first.snd second.snd) leNat)) boolAnd)) boolOr).congr (by
        intro x
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
        rfl)
lemma polynomial_rankLe : PolynomialTime rankLeRealizer := by
  unfold rankLeRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  tree_cost

def rankEntries (rs : List ℕ) : List (ℕ×ℕ) := (List.range rs.length).map fun i=>(rs.getD i 0,i)
def rankEntriesRealizer : Realizer rankEntries := (composition (pair identity (composition listLength range))
  (mapWith (pair (getDFast 0) second))).congr (fun _=>rfl)
lemma polynomial_rankEntries : PolynomialTime rankEntriesRealizer := by
  unfold rankEntriesRealizer
  apply polynomial_congr
  have hr : PolynomialTime (composition (listLength (A:=ℕ)) range) :=
    polynomial_boundedRange polynomial_listLength X (fun x=>by simpa using list_length_le_weight x)
  exact polynomial_composition (polynomial_pair polynomial_identity hr)
    (polynomial_mapWith (polynomial_pair (polynomial_getDFast 0) polynomial_second))
def rankPlan (rs : List ℕ) : List ℕ := ((rankEntries rs).insertionSort rankLe).map Prod.snd
def rankPlanRealizer : Realizer rankPlan := composition (composition rankEntriesRealizer (insertionSort rankLe rankLeRealizer)) (map second)
lemma polynomial_rankPlan : PolynomialTime rankPlanRealizer :=
  polynomial_composition (polynomial_composition polynomial_rankEntries (polynomial_insertionSort rankLe polynomial_rankLe)) (polynomial_map polynomial_second)

lemma rankEntries_ofFn {m : ℕ} (rank : Fin m→ℕ) :
    rankEntries (List.ofFn rank)=List.ofFn (fun i=>(rank i,i.val)) := by
  unfold rankEntries
  rw [List.length_ofFn,map_range_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  simp [List.getD]
lemma zipIdx_rankLE {m : ℕ} (rank : Fin m→ℕ) (a b : Fin m×ℕ) :
    List.zipIdxLE (fun x y=>decide (rank y≤rank x)) a b=
      decide (rankLe (rank a.1,a.2) (rank b.1,b.2)) := by
  apply Bool.eq_iff_iff.mpr
  by_cases hab : rank b.1≤rank a.1 <;> by_cases hba : rank a.1≤rank b.1 <;>
    simp only [List.zipIdxLE,decide_eq_true_eq,ite_true,ite_false,hab,hba]
  all_goals simp only [rankLe,Bool.false_eq_true]
  all_goals try simp only [true_iff,false_iff]
  all_goals omega
lemma zipIdx_ofFn_id (m : ℕ) :
    (List.ofFn (fun i : Fin m=>i)).zipIdx=List.ofFn (fun i : Fin m=>(i,i.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_zipIdx,List.getElem_ofFn,Nat.zero_add]
lemma rankPlan_eq {m : ℕ} (rank : Fin m→ℕ) :
    rankPlan (List.ofFn rank)=(UnitRefresh.Materialized.plan rank).map Fin.val := by
  let xs := List.ofFn (fun i : Fin m=>i)
  let le := fun a b : Fin m=>decide (rank b≤rank a)
  let f := fun a : Fin m×ℕ=>(rank a.1,a.2)
  have hm := List.map_mergeSort (l:=xs.zipIdx) (r:=List.zipIdxLE le) (s:=fun a b=>decide (rankLe a b))
    (f:=f) (fun a _ha b _hb=>zipIdx_rankLE rank a b)
  have hz : xs.zipIdx.map f=List.ofFn (fun i=>(rank i,i.val)) := by
    rw [zipIdx_ofFn_id,List.map_ofFn]
    rfl
  have hfirst : ((xs.zipIdx).mergeSort (List.zipIdxLE le)).map (fun a=>a.1.val)=
      ((xs.zipIdx).mergeSort (List.zipIdxLE le)).map Prod.snd := by
    apply List.map_congr_left
    intro a ha
    rw [List.mem_mergeSort,zipIdx_ofFn_id,List.mem_ofFn] at ha
    obtain ⟨i,rfl⟩:=ha
    rfl
  unfold rankPlan
  rw [rankEntries_ofFn,←List.mergeSort_eq_insertionSort,←hz,←hm, List.map_map]
  change _=(xs.mergeSort le).map Fin.val
  have hm2 := congrArg (List.map Fin.val) (List.mergeSort_zipIdx (l:=xs) (le:=le))
  rw [List.map_map] at hm2
  simpa only [Function.comp_def,f] using hfirst.symm.trans hm2
end MatchingFPRAS.ExecutableHierarchy

end OAI
