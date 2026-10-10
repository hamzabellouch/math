import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeClippedCorrect
import OAI.Combinatorics.MatchingCount.Sampling.TreeFastUnit

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP TreeFraction

lemma fastBranch_eq {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) (b : Fin (n+2)) (hne' : b≠Fin.last (n+1)) :
    fastBranch (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),b.val)=
      UnitRefresh.Materialized.branchCount bags rank parent (Fin.last (n+1)) b := by
  rw [fastBranch,residual_ordered bags b hne',cappedCount_ordered (parent:=parent) _ _ (by
    intro l p hh; have :=hp l p hh; intro e; subst p; omega)]
  let e := UnitRefresh.removePairEquiv (Fin.last (n+1)) b hne'
  have hbe : UnitRefresh.RankedBags (fun i=>bags (e i).val) rank parent := fun v l hl r hr=>hb (e v).val l hl r hr
  rw [UnitRefresh.Materialized.computable_count_eq _ rank parent hbe (fun i=>hne (e i).val) hp]
  rw [Fintype.card_congr (UnitRefresh.ColoredPairing.equiv (UnitRefresh.residualBags bags (Fin.last (n+1)) b) e)]
  exact (UnitRefresh.Materialized.branchCount_eq bags rank parent hb hne hp _ _).symm

lemma fastEdgeCount_eq {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) (b : Fin (n+2)) (c : Fin m) :
    fastEdgeCount (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),(b.val,c.val))=
      UnitRefresh.Materialized.edgeCount bags rank parent (Fin.last (n+1)) (b,c) := by
  rw [fastEdgeCount,valid_eq]
  simp only [decide_eq_true_eq,UnitRefresh.Materialized.edgeCount]
  split_ifs with h
  · exact fastBranch_eq bags rank parent hb hne hp b h.1
  · rfl
lemma fastProbabilities_eq {n m : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) :
    fastProbabilities ((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val)=
      List.ofFn (fun i : Fin ((n+2)*m)=>
        (UnitRefresh.Materialized.edgeCount bags rank parent (Fin.last (n+1)) (finProdFinEquiv.symm i),
         UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))) := by
  unfold fastProbabilities
  simp only [orderedRep,List.length_ofFn,parentRep_length]
  rw [map_range_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  change fastProbability (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),i.val)=_
  rw [fastProbability,parentRep_length,decodeIndex_fin,fastEdgeCount_eq bags rank parent hb hne hp,cappedCount_ordered (parent:=parent) _ _ (by
    intro l p hh; have :=hp l p hh; intro e; subst p; omega)]

lemma fastDraw_eq {n m k : ℕ} (bags : Fin (n+2) → Finset (Fin m))
    (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l)
    (hz : 0<UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))
    (bits : Fin k → Bool) :
    fastDraw (((orderedRep bags,parentRep parent),(UnitRefresh.Materialized.plan rank).map Fin.val),List.ofFn bits)=
      ((UnitRefresh.Materialized.drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k bits).val.val.1.val,
       (UnitRefresh.Materialized.drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k bits).val.val.2.val) := by
  let q : Fin ((n+2)*m) → Fraction := fun i=>
    (UnitRefresh.Materialized.edgeCount bags rank parent (Fin.last (n+1)) (finProdFinEquiv.symm i),
     UnitRefresh.Materialized.count bags parent (UnitRefresh.Materialized.plan rank))
  have hq : ∀ i,0<(q i).2 := fun _=>hz
  have hs : ∑ i,val (q i)=1 :=
    UnitRefresh.Materialized.edgeProbability_sum bags rank parent hb hne hp _ hz
  rw [fastDraw,fastProbabilities_eq bags rank parent hb hne hp]
  change decodeIndex (ExecutableChoice.chooseBits (List.ofFn q,List.ofFn bits), (parentRep parent).length)=_
  rw [ExecutableChoice.chooseBits_values q hq hs,parentRep_length,decodeIndex_fin]
  rfl

end MatchingFPRAS.ExecutableUnit

end OAI
