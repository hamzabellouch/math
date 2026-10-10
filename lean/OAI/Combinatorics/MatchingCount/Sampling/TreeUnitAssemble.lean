import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeUnitBranch

namespace OAI

namespace MatchingFPRAS.UnitRefresh
lemma removePair_last_symm_val {n : ℕ} (b : Fin (n+2)) (hb : b≠Fin.last (n+1))
    (x : withoutPair (Fin.last (n+1)) b) :
    ((removePairEquiv (Fin.last (n+1)) b hb).symm x).val =
      if x.val.val<b.val then x.val.val else x.val.val-1 := by
  let e := removePairEquiv (Fin.last (n+1)) b hb
  let j := e.symm x
  have hj := removePair_last_val b hb j
  have hx : (e j).val.val=x.val.val := congrArg (fun x=>x.val.val) (e.apply_symm_apply x)
  change (e j).val.val=_ at hj
  rw [hx] at hj
  change j.val=_
  by_cases h : j.val<b.val <;> simp only [h,↓reduceIte] at hj
  · rw [ite_eq_left (by omega)]
    omega
  · rw [ite_eq_right (by omega)]
    omega
end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

abbrev Result := List (ℕ×ℕ)
abbrev Frame := ℕ×(ℕ×ℕ)

def unskip (x : ℕ×ℕ) : ℕ := if x.1<x.2 then x.1 else x.1-1
def unskipRealizer : Realizer unskip :=
  (choose less first (composition first predecessor)).congr (fun _=>by simp [unskip])

def assembleAt (x : (Frame×Result)×ℕ) : ℕ×ℕ :=
  let n:=x.1.1.1
  let b:=x.1.1.2.1
  let c:=x.1.1.2.2
  let i:=x.2
  if i=n+1 then (b,c) else if i=b then (n+1,c) else
  let z:=x.1.2.getD (unskip (i,b)) (0,0)
  (skip (z.1,b),z.2)
def assembleAtRealizer : Realizer assembleAt := by
  let n : Realizer (fun x : (Frame×Result)×ℕ=>x.1.1.1) := first.fst.fst
  let b : Realizer (fun x : (Frame×Result)×ℕ=>x.1.1.2.1) := first.fst.snd.fst
  let c : Realizer (fun x : (Frame×Result)×ℕ=>x.1.1.2.2) := first.fst.snd.snd
  let i : Realizer (fun x : (Frame×Result)×ℕ=>x.2) := second
  let a := composition n successor
  let j := composition (pair i b) unskipRealizer
  let z := composition (pair first.snd j) (getD (0,0))
  let r := pair (composition (pair z.fst b) skipRealizer) z.snd
  exact (choose (composition (pair i a) natEqual) (pair b c)
    (choose (composition (pair i b) natEqual) (pair a c) r)).congr (by intro x; simp [assembleAt])

def assemble (x : Frame×Result) : Result :=
  (List.range (x.1.1+2)).map (fun i=>assembleAt (x,i))
def assembleRealizer : Realizer assemble := by
  let n : Realizer (fun x : Frame×Result=>x.1.1+2) :=
    (composition (pair first.fst (constant 2)) add).congr (fun _=>rfl)
  exact (composition (pair identity (composition n range)) (mapWith assembleAtRealizer)).congr (fun _=>rfl)

noncomputable def resultRep {n m : ℕ} {bags : Fin n → Finset (Fin m)}
    (p : UnitRefresh.ColoredPairing bags) : Result := List.ofFn (fun i=>(p.pair.mate i |>.val,p.color i |>.val))

lemma resultRep_getD {n m : ℕ} {bags : Fin n → Finset (Fin m)}
    (p : UnitRefresh.ColoredPairing bags) (i : Fin n) :
    (resultRep p).getD i.val (0,0)=((p.pair.mate i).val,(p.color i).val) := by
  simp [resultRep,List.getD]

lemma assemble_eq {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (c : UnitRefresh.Partner bags (Fin.last (n+1)))
    (p : UnitRefresh.ColoredPairing (fun i=>bags (UnitRefresh.removePairEquiv (Fin.last (n+1)) c.val.1 c.property.1 i).val)) :
    assemble ((n,(c.val.1.val,c.val.2.val)),resultRep p)=
      resultRep ((UnitRefresh.ColoredPairing.map (UnitRefresh.residualBags bags (Fin.last (n+1)) c.val.1)
        (UnitRefresh.removePairEquiv (Fin.last (n+1)) c.val.1 c.property.1) p).insert (Fin.last (n+1)) c) := by
  rw [assemble,map_range_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  let e := UnitRefresh.removePairEquiv (Fin.last (n+1)) c.val.1 c.property.1
  change assembleAt (((n,(c.val.1.val,c.val.2.val)),resultRep p),i.val)=_
  by_cases ha : i=Fin.last (n+1)
  · subst i
    simp only [assembleAt,Fin.val_last,↓reduceIte,UnitRefresh.ColoredPairing.insert,
      UnitRefresh.Pairing.insert,↓reduceDIte,true_or]
  by_cases hb : i=c.val.1
  · subst i
    have han : c.val.1.val≠n+1 := by intro he; exact ha (Fin.ext he)
    simp only [assembleAt,han,↓reduceIte,UnitRefresh.ColoredPairing.insert,
      UnitRefresh.Pairing.insert,ha,↓reduceDIte,or_true,Fin.val_last]
  · let x : UnitRefresh.withoutPair (Fin.last (n+1)) c.val.1 := ⟨i,ha,hb⟩
    have hi : i.val≠n+1 := by intro he; exact ha (Fin.ext he)
    have hi' : i.val≠c.val.1.val := by intro he; exact hb (Fin.ext he)
    have hj : unskip (i.val,c.val.1.val)=(e.symm x).val :=
      (UnitRefresh.removePair_last_symm_val c.val.1 c.property.1 x).symm
    simp only [assembleAt,hi,hi',↓reduceIte,hj,resultRep_getD,
      UnitRefresh.ColoredPairing.insert,UnitRefresh.Pairing.insert,ha,hb,↓reduceDIte,or_self]
    change (skip ((p.pair.mate (e.symm x)).val,c.val.1.val),(p.color (e.symm x)).val)=
      ((e (p.pair.mate (e.symm x))).val.val,(p.color (e.symm x)).val)
    rw [UnitRefresh.removePair_last_val]
    rfl
end MatchingFPRAS.ExecutableUnit

end OAI
