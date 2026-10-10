import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeUnitBranch
import OAI.Combinatorics.MatchingCount.Sampling.TreeCategoricalValues

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP TreeFraction

def decodeIndex (x : ℕ×ℕ) : ℕ×ℕ := (x.1/x.2,x.1%x.2)
def decodeIndexRealizer : Realizer decodeIndex := division

def probability (x : Context×ℕ) : Fraction :=
  (edgeCount (x.1,decodeIndex (x.2,x.1.1.2.length)),count x.1)
def probabilityRealizer : Realizer probability := by
  let m : Realizer (fun x : Context×ℕ=>x.1.1.2.length) := composition first.fst.snd listLength
  let bc := composition (pair second m) decodeIndexRealizer
  exact (pair (composition (pair first bc) edgeCountRealizer)
    (composition first countRealizer)).congr (fun _=>rfl)

def probabilities (x : Context) : List Fraction :=
  (List.range (x.1.1.length*x.1.2.length)).map (fun i=>probability (x,i))
def probabilitiesRealizer : Realizer probabilities := by
  let n : Realizer (fun x : Context=>x.1.1.length) := composition first.fst listLength
  let m : Realizer (fun x : Context=>x.1.2.length) := composition first.snd listLength
  exact (composition (pair identity (composition (composition (pair n m) multiply) range))
    (mapWith probabilityRealizer)).congr (fun _=>rfl)

def draw (x : Context×List Bool) : ℕ×ℕ :=
  decodeIndex (ExecutableChoice.chooseBits (probabilities x.1,x.2),x.1.1.2.length)
def drawRealizer : Realizer draw :=
  (composition (pair (composition (pair (composition first probabilitiesRealizer) second)
      ExecutableChoice.chooseBitsRealizer) (composition first.fst.snd listLength))
    decodeIndexRealizer).congr (fun _=>rfl)

lemma decodeIndex_fin {n m : ℕ} (i : Fin (n*m)) :
    decodeIndex (i.val,m)=((finProdFinEquiv.symm i).1.val,(finProdFinEquiv.symm i).2.val) := rfl

lemma probabilities_eq {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) :
    probabilities ((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val)=
      List.ofFn (fun i : Fin ((n+2)*m)=>
        (UnitRefresh.Materialized.edgeCount bags rank parent (Fin.last (n+1)) (finProdFinEquiv.symm i),
         UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))) := by
  unfold probabilities
  simp only [orderedRep,List.length_ofFn,parentRep_length]
  rw [map_range_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  change probability (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),i.val)=_
  rw [probability,parentRep_length,decodeIndex_fin,edgeCount_eq bags rank parent hb hne hp,count_ordered]

lemma draw_eq {n m k : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))
    (bits : Fin k → Bool) :
    draw (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),List.ofFn bits)=
      ((UnitRefresh.Materialized.drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k bits).val.val.1.val,
       (UnitRefresh.Materialized.drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k bits).val.val.2.val) := by
  let q : Fin ((n+2)*m) → Fraction := fun i=>
    (UnitRefresh.Materialized.edgeCount bags rank parent (Fin.last (n+1)) (finProdFinEquiv.symm i),
     UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))
  have hq : ∀ i,0<(q i).2 := fun _=>hz
  have hs : ∑ i,val (q i)=1 :=
    UnitRefresh.Materialized.edgeProbability_sum bags rank parent hb hne hp _ hz
  rw [draw,probabilities_eq bags rank parent hb hne hp]
  change decodeIndex (ExecutableChoice.chooseBits (List.ofFn q,List.ofFn bits), (parentRep parent).length)=_
  rw [ExecutableChoice.chooseBits_values q hq hs,parentRep_length,decodeIndex_fin]
  rfl

end MatchingFPRAS.ExecutableUnit

end OAI
