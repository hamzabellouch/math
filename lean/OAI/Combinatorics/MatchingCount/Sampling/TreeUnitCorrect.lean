import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.RemainingBags
import OAI.Combinatorics.MatchingCount.Sampling.TreeUnitSampler

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open ExecutableDP UnitRefresh.Materialized

lemma rawSample_eq (n : ℕ) {m k : ℕ} (bags : Fin n → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (plan rank))
    (bits : Fin n → Fin k → Bool) (bs : Bits)
    (hbs : ∀ i : Fin n,bs.getD i.val []=List.ofFn (bits i))
    (fuel : ℕ) (hfuel : n≤fuel) :
    rawSample fuel ((orderedRep bags,parentRep parent),(plan rank).map Fin.val) bs=
      resultRep (sampleUnit k n bags rank parent hb hne hp hz bits) := by
  induction n using Nat.strong_induction_on generalizing fuel with
  | h n ih =>
    cases n with
    | zero =>
      cases fuel <;> simp [rawSample,orderedRep,resultRep]
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
        have hc := selected_eq_of_getD bags rank parent hb hne hp hz bits bs (hbs a)
        change selected (((orderedRep bags,parentRep parent),(plan rank).map Fin.val),bs)=
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
          have hr := ih n (by omega) bags' hb' hne' hz' bits' hbits' fuel (by omega)
          have hl : (orderedRep bags).length=n+2 := List.length_ofFn
          rw [rawSample]
          simp only [hl,show 2≤n+2 by omega,↓reduceIte,hc,hnext,Nat.add_sub_cancel]
          rw [hr]
          rw [sampleUnit_step]
          exact assemble_eq bags c.val _

lemma sample_eq {n m k : ℕ} (bags : Fin n → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (plan rank))
    (bits : Fin n → Fin k → Bool) :
    sample (((orderedRep bags,parentRep parent),(plan rank).map Fin.val),List.ofFn (fun i=>List.ofFn (bits i)))=
      resultRep (sampleUnit k n bags rank parent hb hne hp hz bits) := by
  unfold sample
  apply rawSample_eq n bags rank parent hb hne hp hz bits
  · intro i
    simp only [List.getD,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some]
  · simp only [orderedRep,List.length_ofFn,le_refl]
end MatchingFPRAS.ExecutableUnit

end OAI
