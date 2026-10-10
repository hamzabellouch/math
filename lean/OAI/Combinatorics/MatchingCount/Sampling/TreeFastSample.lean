import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.RemainingBags
import OAI.Combinatorics.MatchingCount.Sampling.TreeFastDescent
import OAI.Combinatorics.MatchingCount.Sampling.TreeFastUnitCorrect
import OAI.Combinatorics.MatchingCount.Machines.TreeCappedAssembly

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

def fastRawSample (cap : Context) : ℕ → Context → Bits → Result
  | 0,_,_ => []
  | f+1,x,bits => if 2≤x.1.1.length then
      let c:=fastSelected (x,bits)
      clippedAssemble (cap,((x.1.1.length-2,c),fastRawSample cap f (nextContext (x,c)) bits))
    else []
def unwindClipped (cap : Context) (fs : List Frame) (r : Result) : Result :=
  (fs.foldl (fun z f=>assemblyFoldStep (f,z)) (cap,r)).2
lemma fastDescend_unwind (cap : Context) (f : ℕ) (x : Context) (bs : Bits) (fs : List Frame) :
    unwindClipped cap (countDown (fun y : ℕ×State=>fastStep y.2) f (x,(bs,fs))).2.2 []=
      unwindClipped cap fs (fastRawSample cap f x bs) := by
  induction f generalizing x bs fs with
  | zero => rfl
  | succ f ih =>
    rw [countDown]
    by_cases h : 2≤x.1.1.length
    · have he : fastStep (x,(bs,fs))=(nextContext (x,fastSelected (x,bs)),(bs,(x.1.1.length-2,fastSelected (x,bs))::fs)) := by simp only [fastStep,h,↓reduceIte]
      rw [he,ih]
      simp only [fastRawSample,h,↓reduceIte]
      rfl
    · have he : fastStep (x,(bs,fs))=(x,(bs,fs)) := by simp only [fastStep,h,↓reduceIte]
      rw [he,ih]
      simp only [fastRawSample,h,↓reduceIte]
      have hz : fastRawSample cap f x bs=[] := by cases f <;> simp [fastRawSample,h]
      rw [hz]

def fastSample (x : Context×Bits) : Result := fastRawSample x.1 x.1.1.1.length x.1 x.2
def fastSampleRealizer : Realizer fastSample :=
  (composition (composition (pair fastDescendRealizer.snd.snd (pair first (constant ([] : Result))))
    (fold assemblyFoldStepRealizer)) second).congr (by
      intro x
      exact (fastDescend_unwind x.1 _ _ _ []).trans rfl)
lemma polynomial_fastSample : PolynomialTime fastSampleRealizer := by
  unfold fastSampleRealizer
  apply polynomial_congr
  apply polynomial_composition _ polynomial_second
  apply polynomial_composition _ polynomial_assemblyFold
  exact polynomial_pair (polynomial_snd (polynomial_snd polynomial_fastDescend))
    (polynomial_pair polynomial_first (polynomial_constant []))

lemma fastSelected_eq_of_getD {n m k : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))
    (bits : Fin (n+2) → Fin k → Bool) (bs : Bits)
    (hbs : bs.getD (n+1) []=List.ofFn (bits (Fin.last (n+1)))) :
    fastSelected (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),bs)=
      ((UnitRefresh.Materialized.drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k (bits (Fin.last (n+1)))).val.val.1.val,
       (UnitRefresh.Materialized.drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k (bits (Fin.last (n+1)))).val.val.2.val) := by
  have hl : (orderedRep bags).length-1=n+1 := by simp only [orderedRep,List.length_ofFn]; omega
  unfold fastSelected
  rw [hl,hbs]
  exact fastDraw_eq bags rank parent hb hne hp hz _

open UnitRefresh.Materialized

lemma fastRawSample_eq (cap : Context) (n : ℕ) {m k : ℕ}
    (hcapn : n≤cap.1.1.length) (hcapm : m≤cap.1.2.length) (bags : Fin n → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (plan rank))
    (bits : Fin n → Fin k → Bool) (bs : Bits)
    (hbs : ∀ i : Fin n,bs.getD i.val []=List.ofFn (bits i))
    (fuel : ℕ) (hfuel : n≤fuel) :
    fastRawSample cap fuel ((orderedRep bags,parentRep parent),(plan rank).map Fin.val) bs=
      resultRep (sampleUnit k n bags rank parent hb hne hp hz bits) := by
  induction n using Nat.strong_induction_on generalizing fuel with
  | h n ih =>
    cases n with
    | zero =>
      cases fuel <;> simp [fastRawSample,orderedRep,resultRep]
    | succ n =>
      cases n with
      | zero =>
        have hzero := singleton_count_zero bags rank parent hb hne hp
        omega
      | succ n =>
        let a : Fin (n+2) := Fin.last (n+1)
        let c := drawEdge bags rank parent hb hne hp a hz k (bits a)
        let bags' := remainingBags bags a c.val
        have hb' := remainingRanked bags rank parent hb a c.val
        have hne' := remainingNonempty bags hne a c.val
        have hz' := remainingPositive bags rank parent hb hne hp a c
        let bits' : Fin n → Fin k → Bool := fun i=>bits i.castSucc.castSucc
        have hbits' : ∀ i : Fin n,bs.getD i.val []=List.ofFn (bits' i) :=
          fun i=>hbs i.castSucc.castSucc
        have hc := fastSelected_eq_of_getD bags rank parent hb hne hp hz bits bs (hbs a)
        change fastSelected (((orderedRep bags,parentRep parent),(plan rank).map Fin.val),bs)=
          (c.val.val.1.val,c.val.val.2.val) at hc
        have hnext : nextContext (((orderedRep bags,parentRep parent),(plan rank).map Fin.val),
            (c.val.val.1.val,c.val.val.2.val))=
            ((orderedRep bags',parentRep parent),(plan rank).map Fin.val) := by
          unfold nextContext
          rw [residual_ordered bags c.val.val.1 c.val.property.1]
          rfl
        cases fuel with
        | zero => omega
        | succ fuel =>
          have hr := ih n (by omega) (by omega) bags' hb' hne' hz' bits' hbits' fuel (by omega)
          have hl : (orderedRep bags).length=n+2 := List.length_ofFn
          rw [fastRawSample]
          simp only [hl,show 2≤n+2 by omega,↓reduceIte,hc,hnext,Nat.add_sub_cancel]
          rw [hr]
          rw [sampleUnit_step]
          exact clippedAssemble_eq cap hcapn hcapm bags c.val _

lemma fastSample_eq {n m k : ℕ} (bags : Fin n → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (plan rank))
    (bits : Fin n → Fin k → Bool) :
    fastSample (((orderedRep bags,parentRep parent),(plan rank).map Fin.val),List.ofFn (fun i=>List.ofFn (bits i)))=
      resultRep (sampleUnit k n bags rank parent hb hne hp hz bits) := by
  unfold fastSample
  apply fastRawSample_eq _ n (by simp [orderedRep]) (by simp [parentRep_length]) bags rank parent hb hne hp hz bits
  · intro i
    simp only [List.getD,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some]
  · simp only [orderedRep,List.length_ofFn,le_refl]
end MatchingFPRAS.ExecutableUnit

end OAI
