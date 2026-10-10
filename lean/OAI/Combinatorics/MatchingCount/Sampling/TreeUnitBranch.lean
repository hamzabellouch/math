import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Plan
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPRepresentation

namespace OAI

namespace MatchingFPRAS.UnitRefresh
lemma gapEquiv_val {n : ℕ} (a : Fin (n+1)) (i : Fin n) :
    (gapEquiv a i).val=a.succAbove i := rfl
lemma removePair_last_val {n : ℕ} (b : Fin (n+2)) (hb : b≠Fin.last (n+1)) (i : Fin n) :
    (removePairEquiv (Fin.last (n+1)) b hb i).val.val=if i.val<b.val then i.val else i.val+1 := by
  let e := gapEquiv (Fin.last (n+1))
  let b' := e.symm ⟨b,hb⟩
  have hb' : b'.val=b.val := by
    have h := congrArg (fun x=>x.val.val) (e.apply_symm_apply ⟨b,hb⟩)
    simpa only [e,gapEquiv_val,Fin.succAbove_last,Fin.val_castSucc] using h
  change ((gapEquiv (Fin.last (n+1)) (gapEquiv b' i).val).val).val=_
  rw [gapEquiv_val,Fin.succAbove_last,Fin.val_castSucc,gapEquiv_val]
  by_cases hi : i.val<b.val
  · rw [ite_eq_left hi,Fin.succAbove_of_castSucc_lt _ _ (show i.castSucc < b' from by change i.val < b'.val; omega)]
    rfl
  · rw [ite_eq_right hi,Fin.succAbove_of_le_castSucc _ _ (show b' ≤ i.castSucc from by change b'.val ≤ i.val; omega)]
    rfl
end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

def skip (x : ℕ×ℕ) : ℕ := if x.1<x.2 then x.1 else x.1+1
def skipRealizer : Realizer skip := (choose less first (composition first successor)).congr (fun _=>by simp [skip])

def residual (x : Bags×ℕ) : Bags :=
  (List.range (x.1.length-2)).map (fun i=>x.1.getD (skip (i,x.2)) [])
def residualRealizer : Realizer residual := by
  let p : Realizer (fun x : (Bags×ℕ)×ℕ=>(x.1.1,skip (x.2,x.1.2))) :=
    pair first.fst (composition (pair second first.snd) skipRealizer)
  let n : Realizer (fun x : Bags×ℕ=>x.1.length-2) := composition (pair (composition first listLength) (constant 2)) subtract
  exact (composition (pair identity (composition n range))
    (mapWith (composition p (getD ([] : Bag))))).congr (fun _=>rfl)

lemma residual_ordered {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (b : Fin (n+2)) (hb : b≠Fin.last (n+1)) :
    residual (orderedRep bags,b.val)=
      orderedRep (fun i=>bags (UnitRefresh.removePairEquiv (Fin.last (n+1)) b hb i).val) := by
  unfold residual orderedRep
  simp only [List.length_ofFn, Nat.add_sub_cancel]
  rw [map_range_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  have hv := UnitRefresh.removePair_last_val b hb i
  have hl : skip (i.val,b.val)<n+2 := by simp only [skip]; split_ifs <;> omega
  simp only [List.getD,List.getElem?_ofFn,hl,↓reduceDIte,Option.getD_some]
  congr 2
  apply Fin.ext
  exact hv.symm

abbrev Context := CountInput

def valid (x : Context×(ℕ×ℕ)) : Bool :=
  let bs:=x.1.1.1
  let b:=x.2.1
  let c:=x.2.2
  decide (b≠bs.length-1) && decide (c∈bs.getD (bs.length-1) []) && decide (c∈bs.getD b [])

def validRealizer : Realizer valid := by
  let bs : Realizer (fun x : Context×(ℕ×ℕ)=>x.1.1.1) := first.fst.fst
  let b : Realizer (fun x : Context×(ℕ×ℕ)=>x.2.1) := second.fst
  let c : Realizer (fun x : Context×(ℕ×ℕ)=>x.2.2) := second.snd
  let a := composition (composition bs listLength) predecessor
  let ba := composition (pair bs a) (getD ([] : Bag))
  let bb := composition (pair bs b) (getD ([] : Bag))
  let p := composition (composition (pair b a) natEqual) boolNot
  let q := composition (pair ba c) membership
  let r := composition (pair bb c) membership
  exact (composition (pair (composition (pair p q) boolAnd) r) boolAnd).congr (by intro x; simp [valid])

def branch (x : Context×ℕ) : ℕ :=
  count ((residual (x.1.1.1,x.2),x.1.1.2),x.1.2)
def branchRealizer : Realizer branch :=
  (composition (pair (pair (composition (pair first.fst.fst second) residualRealizer) first.fst.snd)
    first.snd) countRealizer).congr (fun _=>rfl)

def edgeCount (x : Context×(ℕ×ℕ)) : ℕ := if valid x then branch (x.1,x.2.1) else 0
def edgeCountRealizer : Realizer edgeCount :=
  (choose validRealizer (composition (pair first second.fst) branchRealizer) (constant 0)).congr (fun _=>rfl)

lemma branch_eq {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) (b : Fin (n+2)) (hne' : b≠Fin.last (n+1)) :
    branch (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),b.val)=
      UnitRefresh.Materialized.branchCount bags rank parent (Fin.last (n+1)) b := by
  rw [branch,residual_ordered bags b hne',count_ordered]
  let e := UnitRefresh.removePairEquiv (Fin.last (n+1)) b hne'
  have hbe : UnitRefresh.RankedBags (fun i=>bags (e i).val) rank parent := fun v l hl r hr=>hb (e v).val l hl r hr
  rw [UnitRefresh.Materialized.computable_count_eq _ rank parent hbe (fun i=>hne (e i).val) hp]
  rw [Fintype.card_congr (UnitRefresh.ColoredPairing.equiv (UnitRefresh.residualBags bags (Fin.last (n+1)) b) e)]
  exact (UnitRefresh.Materialized.branchCount_eq bags rank parent hb hne hp _ _).symm

lemma valid_eq {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (ps : Parents) (ls : List ℕ) (b : Fin (n+2)) (c : Fin m) :
    valid (((orderedRep bags,ps),ls),(b.val,c.val))=
      decide (UnitRefresh.Materialized.validBranch bags (Fin.last (n+1)) (b,c)) := by
  have ha : n+2-1=n+1 := by omega
  have hget (i : Fin (n+2)) : (orderedRep bags).getD i.val []=bagRep (bags i) := by
    simp only [orderedRep,List.getD,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some]
  have hgeta : (orderedRep bags).getD (n+1) []=bagRep (bags (Fin.last (n+1))) := hget (Fin.last (n+1))
  apply Bool.eq_iff_iff.mpr
  simp only [valid,show (orderedRep bags).length=n+2 from List.length_ofFn,ha,
    hgeta,hget,Bool.and_eq_true,decide_eq_true_eq,mem_bagRep,
    UnitRefresh.Materialized.validBranch]
  constructor
  · rintro ⟨⟨hb,hc⟩,hd⟩
    apply decide_eq_true
    exact ⟨by intro he; exact hb (congrArg Fin.val he),hc,hd⟩
  · intro h
    have hh := of_decide_eq_true h
    exact ⟨⟨by intro he; exact hh.1 (Fin.ext he),hh.2.1⟩,hh.2.2⟩

lemma edgeCount_eq {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) (b : Fin (n+2)) (c : Fin m) :
    edgeCount (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),(b.val,c.val))=
      UnitRefresh.Materialized.edgeCount bags rank parent (Fin.last (n+1)) (b,c) := by
  rw [edgeCount,valid_eq]
  simp only [decide_eq_true_eq,UnitRefresh.Materialized.edgeCount]
  split_ifs with h
  · exact branch_eq bags rank parent hb hne hp b h.1
  · rfl
end MatchingFPRAS.ExecutableUnit

end OAI
