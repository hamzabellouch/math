import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeNumericStatisticsCorrect
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeAdaptiveArithmetic

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableStatistics ExecutableLadder ExecutableEstimator

abbrev Summaries := (Fraction×Fraction)×List (ℕ×Fraction)

def rawProbe (x : (Reweights×List (ExecutableMarking.Marks ℕ))×ℕ) : ℕ×Fraction :=
  (x.2,averageProbe reweight ((x.1.1,x.2),x.1.2))
def rawProbeRealizer : Realizer rawProbe := (pair second
  (composition (pair (pair first.fst second) first.snd) (averageProbeRealizer reweightRealizer natEqual))).congr (fun _=>rfl)
lemma polynomial_rawProbe : PolynomialTime rawProbeRealizer := by
  unfold rawProbeRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_averageProbe polynomial_reweight polynomial_natEqual
  tree_cost

def summaries (x : Inputs) : Summaries :=
  ((ratio (averageA x.2,averageD reweight (x.1.1,x.2)),averageD reweight (x.1.1,x.2)),
   x.1.2.2.map (fun e=>rawProbe ((x.1.1,x.2),e)))
def summariesRealizer : Realizer summaries :=
  (pair (pair (composition (pair (composition second averageARealizer)
      (composition (pair first.fst second) (averageDRealizer reweightRealizer))) ratioRealizer)
    (composition (pair first.fst second) (averageDRealizer reweightRealizer)))
    (composition (pair (pair first.fst second) first.snd.snd) (mapWith rawProbeRealizer))).congr (fun _=>rfl)
lemma polynomial_summaries : PolynomialTime summariesRealizer := by
  unfold summariesRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_averageA (E:=ℕ)
  have := polynomial_averageD polynomial_reweight
  have := polynomial_ratio
  have := polynomial_rawProbe
  tree_cost

lemma summaries_rep {E : Type} [Fintype E] [LinearOrder E] {S : ℕ}
    (s : Fin S→Finset E) (m : Fin S→E→Fin 3)
    (r : E→ℚ) (hr : ∀ e,0≤r e) (D : ℕ) (keys : List E) :
    summaries ((reweightsRep r,(D,keys.map index)),List.ofFn (fun i=>numericMarks (s i) (m i)))=
      ((TreeFraction.repr (Counting.ratioEstimate ((∑ i,scalarA s m i)/(S:ℚ))
        ((∑ i,scalarD s m r i)/(S:ℚ))),TreeFraction.repr ((∑ i,scalarD s m r i)/(S:ℚ))),
       keys.map (fun e=>(index e,TreeFraction.repr ((∑ i,scalarProbe s m r e i)/(S:ℚ))))) := by
  have hs : List.ofFn (fun i=>numericMarks (s i) (m i))=
      sampleRep (fun i=>Numbered.set (s i)) (fun i=>extend 0 (m i)) := by
    simp only [sampleRep,numericMarks_eq]
  rw [summaries,hs]
  dsimp only
  rw [averageA_rep,averageD_rep _ _ reweight (reweightsRep r) (extend 1 r)
    (extend_nonneg r hr) (reweight_rep r)]
  simp only [scalarA_numbered,scalarD_numbered]
  have ha (i : Fin S) : 0 ≤ scalarA s m i := by
    unfold scalarA; split_ifs <;> norm_num
  have hd (i : Fin S) : 0 ≤ scalarD s m r i := by
    unfold scalarD; split_ifs
    · exact Finset.prod_nonneg (fun e _=>hr e)
    · exact le_rfl
  rw [ratio_rep _ _ (div_nonneg (Finset.sum_nonneg (fun i _=>ha i)) (Nat.cast_nonneg _))
    (div_nonneg (Finset.sum_nonneg (fun i _=>hd i)) (Nat.cast_nonneg _))]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro e _he
  unfold rawProbe
  dsimp only [Function.comp_def]
  rw [averageProbe_rep _ _ reweight (reweightsRep r) (extend 1 r)
    (extend_nonneg r hr) (reweight_rep r)]
  simp only [scalarProbe_numbered]

abbrev Bindings := List ((ℕ×ℕ)×ℕ)
def logicalProbes (x : Bindings×List (ℕ×Fraction)) : ExecutableAdaptive.ProbeTable :=
  x.1.map (fun z=>(z.1,lookup (0,1) (x.2,z.2)))
def logicalProbesRealizer : Realizer logicalProbes := (composition (pair second first)
  (mapWith (pair second.fst (composition (pair first second.snd) (lookupRealizer (0,1) natEqual))))).congr (fun _=>rfl)
lemma polynomial_logicalProbes : PolynomialTime logicalProbesRealizer := by
  unfold logicalProbesRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_lookup ((0,1) : Fraction) polynomial_natEqual
  tree_cost

lemma logicalProbes_rep {E : Type} [Fintype E] [LinearOrder E] {n : ℕ}
    (c : Enlargement.LogicalEdge (Fin n)→E) (keys : List E) (hk : ∀ e,e∈keys) (z : E→ℚ) :
    logicalProbes ((List.ofFn (UnitRefresh.orderedEnum (Enlargement.LogicalEdge (Fin n)))).map
        (fun e=>(ExecutableSource.logicalRepr e,index (c e))),
      keys.map (fun e=>(index e,TreeFraction.repr (z e))))=
      (List.ofFn (UnitRefresh.orderedEnum (Enlargement.LogicalEdge (Fin n)))).map
        (fun e=>(ExecutableSource.logicalRepr e,TreeFraction.repr (z (c e)))) := by
  unfold logicalProbes
  rw [List.map_map]
  apply List.map_congr_left
  intro e _he
  dsimp only [Function.comp_def]
  rw [lookup_image (0,1) keys index (fun e=>TreeFraction.repr (z e)) index_injective (c e) (hk _)]

abbrev UpdateConfig := (ℕ×List ℕ)×(Bindings×ExecutableScaling.Vector)
def finishUpdate (x : UpdateConfig×Summaries) : Fraction×ExecutableScaling.Vector :=
  (x.2.1.1,ExecutableAdaptive.updateVector
    (ExecutableAdaptive.estimateMatrix (((x.1.1.1,x.2.1.2),logicalProbes (x.1.2.1,x.2.2)),x.1.1.2),x.1.2.2))
def finishUpdateRealizer : Realizer finishUpdate := (pair second.fst.fst
  (composition (pair (composition (pair (pair (pair first.fst.fst second.fst.snd)
    (composition (pair first.snd.fst second.snd) logicalProbesRealizer)) first.fst.snd)
      ExecutableAdaptive.estimateMatrixRealizer) first.snd.snd) ExecutableAdaptive.updateVectorRealizer)).congr (fun _=>rfl)
lemma polynomial_finishUpdate : PolynomialTime finishUpdateRealizer := by
  unfold finishUpdateRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_logicalProbes
  have := ExecutableAdaptive.polynomial_estimateMatrix
  have := ExecutableAdaptive.polynomial_updateVector
  tree_cost

end MatchingFPRAS.NumericMarking

end OAI
