import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeStageUpdateCorrect
import OAI.Combinatorics.MatchingCount.Algorithm.TreeStatistics

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableStatistics ExecutableLadder

  ExecutableEstimator ExecutableBottleneck ExecutableScaling ExecutableAdaptive ExecutableSource
open Finset Transport Enlargement

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : Fin G.n→Fin G.n→ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : Fin G.n→Fin G.n→ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _

noncomputable def sourceUpdateConfig (s : FiniteTrial.ScaleState G j) (K : ℕ) : UpdateConfig :=
  ((FiniteTrial.sourceD (G:=G) K,List.range G.n),
    ((List.ofFn (UnitRefresh.orderedEnum (LogicalEdge (Fin G.n)))).map
      (fun e=>(logicalRepr e,index (RationalSource.centralEdge s.activity K e))),vectorRep s.scale))
noncomputable def sourceStatisticsInput (s : FiniteTrial.ScaleState G j) (K : ℕ)
    (x : Fin S→RationalSource.Marked s.activity K) : Inputs :=
  ((reweightsRep (RationalSource.bagReweight s.activity s.nextActivity K),
    (FiniteTrial.sourceD (G:=G) K,(sourceKeys s.activity K).map index)),sourceSamples s.activity K x)

lemma scaleState_update_rep (hn : 2≤G.n) (s : FiniteTrial.ScaleState G j)
    (x : Fin S→RationalSource.Marked s.activity K) :
    finishUpdate (sourceUpdateConfig s K,summaries (sourceStatisticsInput s K x))=
      (TreeFraction.repr (s.ratioEstimate x),vectorRep (s.update hn x).scale) := by
  unfold sourceStatisticsInput
  rw [summaries_source s.activity s.nextActivity K x
    (fun i j=>(s.activity_pos i j).le) (fun i j=>(s.nextActivity_pos i j).le)]
  let z := fun e=>(∑ i,scalarProbe (fun j=>(x j).1.val)
    (fun j=>selectedMarks (x j).1.val (x j).2)
    (RationalSource.bagReweight s.activity s.nextActivity K) e i)/(S:ℚ)
  have hr := reweight_nonneg s.activity s.nextActivity
    (fun i j=>(s.activity_pos i j).le) (fun i j=>(s.nextActivity_pos i j).le) K
  have hz : ∀ e,0≤z e := by
    intro e
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro i _
    unfold scalarProbe
    split_ifs
    · exact Finset.prod_nonneg (fun a _=>hr a)
    · exact le_rfl
  have hd : 0≤FiniteTrial.sampleAverage (RationalSource.observableD s.activity s.nextActivity K) x := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro i _
    unfold RationalSource.observableD
    split_ifs
    · exact Finset.prod_nonneg (fun a _=>hr a)
    · exact le_rfl
  change finishUpdate (((FiniteTrial.sourceD (G:=G) K,List.range G.n),
    ((List.ofFn (UnitRefresh.orderedEnum (LogicalEdge (Fin G.n)))).map
      (fun e=>(logicalRepr e,index (RationalSource.centralEdge s.activity K e))),vectorRep s.scale)),
    ((TreeFraction.repr (s.ratioEstimate x),TreeFraction.repr
      (FiniteTrial.sampleAverage (RationalSource.observableD s.activity s.nextActivity K) x)),
      (sourceKeys s.activity K).map (fun e=>(index e,TreeFraction.repr (z e)))))=_
  rw [finishUpdate_rep hn (RationalSource.centralEdge s.activity K) (sourceKeys s.activity K)
    (mem_sourceKeys s.activity K) z hz _ _ _ hd s.scale (fun i=>(s.positive i).le)]
  have he : z ∘ RationalSource.centralEdge s.activity K=
      (fun e=>FiniteTrial.sampleAverage (RationalSource.observableProbe s.activity s.nextActivity K e) x) := by
    funext e
    simp only [z,Function.comp_def,scalarProbe_source,FiniteTrial.sampleAverage]
  rw [he]
  rfl
end MatchingFPRAS.NumericMarking

end OAI
