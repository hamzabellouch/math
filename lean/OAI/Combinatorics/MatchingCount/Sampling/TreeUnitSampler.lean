import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeUnitDraw
import OAI.Combinatorics.MatchingCount.Sampling.TreeUnitAssemble

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

abbrev Bits := List (List Bool)
abbrev State := Context×(Bits×List Frame)
def nextContext (x : Context×(ℕ×ℕ)) : Context :=
  ((residual (x.1.1.1,x.2.1),x.1.1.2),x.1.2)
def nextContextRealizer : Realizer nextContext :=
  (pair (pair (composition (pair first.fst.fst second.fst) residualRealizer) first.fst.snd) first.snd).congr (fun _=>rfl)
def selected (x : Context×Bits) : ℕ×ℕ := draw (x.1,x.2.getD (x.1.1.1.length-1) [])
def selectedRealizer : Realizer selected := by
  let n : Realizer (fun x : Context×Bits=>x.1.1.1.length-1) := composition (composition first.fst.fst listLength) predecessor
  exact (composition (pair first (composition (pair second n) (getD []))) drawRealizer).congr (fun _=>rfl)
def step (x : State) : State :=
  if 2≤x.1.1.1.length then
    let c:=selected (x.1,x.2.1)
    (nextContext (x.1,c),(x.2.1,(x.1.1.1.length-2,c)::x.2.2))
  else x
def stepRealizer : Realizer step := by
  let n : Realizer (fun x : State=>x.1.1.1.length) := composition first.fst.fst listLength
  let c : Realizer (fun x : State=>selected (x.1,x.2.1)) := (composition (f:=fun x : State=>(x.1,x.2.1)) (pair first second.fst) selectedRealizer).congr (fun _=>rfl)
  let ctx := composition (pair first c) nextContextRealizer
  let k := composition (pair n (constant 2)) subtract
  let fs := composition (pair (pair k c) second.snd) listCons
  let r := pair ctx (pair second.fst fs)
  exact (choose (composition (composition (pair n (constant 2)) less) boolNot) r identity).congr (by
    intro x; simp [step,Nat.succ_le_iff])

def rawSample : ℕ → Context → Bits → Result
  | 0,_,_ => []
  | f+1,x,bits => if 2≤x.1.1.length then
      let c:=selected (x,bits)
      assemble ((x.1.1.length-2,c),rawSample f (nextContext (x,c)) bits)
    else []
def unwind (fs : List Frame) (r : Result) : Result := fs.foldl (fun z a=>assemble (a,z)) r
lemma descend_unwind (f : ℕ) (x : Context) (bs : Bits) (fs : List Frame) :
    unwind (countDown (fun y : ℕ×State=>step y.2) f (x,(bs,fs))).2.2 []=
      unwind fs (rawSample f x bs) := by
  induction f generalizing x bs fs with
  | zero => rfl
  | succ f ih =>
    rw [countDown]
    by_cases h : 2≤x.1.1.length
    · have he : step (x,(bs,fs))=(nextContext (x,selected (x,bs)),(bs,(x.1.1.length-2,selected (x,bs))::fs)) := by simp only [step,h,↓reduceIte]
      rw [he,ih]
      simp only [rawSample,h,↓reduceIte]
      rfl
    · have he : step (x,(bs,fs))=(x,(bs,fs)) := by simp only [step,h,↓reduceIte]
      rw [he,ih]
      simp only [rawSample,h,↓reduceIte]
      have hz : rawSample f x bs=[] := by cases f <;> simp [rawSample,h]
      rw [hz]

def sample (x : Context×Bits) : Result := rawSample x.1.1.1.length x.1 x.2
def sampleRealizer : Realizer sample := by
  let st : Realizer (fun x : Context×Bits=>(x.1,(x.2,([] : List Frame)))) := pair first (pair second (constant []))
  let fuel : Realizer (fun x : Context×Bits=>x.1.1.1.length) := composition first.fst.fst listLength
  let run := composition (pair fuel st) (iterateDown (composition second stepRealizer))
  let fs := run.snd.snd
  let res := composition (pair fs (constant ([] : Result))) (fold assembleRealizer)
  exact res.congr (by intro x; exact (descend_unwind _ _ _ []).trans rfl)

lemma selected_eq_of_getD {n m k : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))
    (bits : Fin (n+2) → Fin k → Bool) (bs : Bits)
    (hbs : bs.getD (n+1) []=List.ofFn (bits (Fin.last (n+1)))) :
    selected (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),bs)=
      ((UnitRefresh.Materialized.drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k (bits (Fin.last (n+1)))).val.val.1.val,
       (UnitRefresh.Materialized.drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k (bits (Fin.last (n+1)))).val.val.2.val) := by
  have hl : (orderedRep bags).length-1=n+1 := by simp only [orderedRep,List.length_ofFn]; omega
  unfold selected
  rw [hl,hbs]
  exact draw_eq bags rank parent hb hne hp hz _
end MatchingFPRAS.ExecutableUnit

end OAI
