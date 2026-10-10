import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreePreparedMarked
import OAI.Combinatorics.MatchingCount.Algorithm.TreeNumericStatisticsCorrect

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableMarking ExecutableStatistics

  ExecutableLadder UnitRefresh NumericLadder Replica.Ladder Transport
abbrev StageInput := ((Reweights×(ℕ×List ℕ))×SampleContext)×List SampleBits

def stage (x : StageInput) : Fraction×List (ℕ×Fraction) :=
  statistics (x.1.1,sampleMany (x.1.2,x.2))
def stageRealizer : Realizer stage := (composition
  (pair first.fst (composition (pair first.snd second) sampleManyRealizer))
  statisticsRealizer).congr (fun _=>rfl)
lemma polynomial_stage : PolynomialTime stageRealizer := by
  unfold stageRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_sampleMany
  have := polynomial_statistics
  tree_cost

theorem stage_post : ∃ p : Polynomial ℕ,∀ x : StageInput,∀ t : ℕ,
    p.eval (TreePost.packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (TreePost.machine stageRealizer.program) (TreePost.packed x) coins).state=none ∧
      (run (TreePost.machine stageRealizer.program) (TreePost.packed x) coins).tape.right₀=
        Turing.ListBlank.mk (TreePost.packed (stage x)) :=
  TreePost.polynomial_compiles stageRealizer polynomial_stage

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L} {G : SimpleGraph L}
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)
variable (rank : L→ℕ) (parent : L→Option L)
variable (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
variable (hp : ∀ l p,parent l=some p → rank p<rank l)

lemma stage_source (ft fq : List Bool) (hq : 0<fq.length)
    (w : BagEdge bags→ℚ) (hw : ∀ e,0≤w e) (M : BagPM bags)
    (a : ExecutableDP.Bags) (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags)))
    (f : BagEdge bags→WeightedOptions (Fin 3)) (r : BagEdge bags→ℚ) (hr : ∀ e,0≤r e)
    (D : ℕ) (keys : List (BagEdge bags))
    {S k n km : ℕ} (bits : Fin S→Fin n→ScanBits V k) (mb : Fin S→BagEdge bags→Fin km→Bool) :
    let s := fun j=>(ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) (bits j)
      (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length)))).val
    let m := fun j e=>(f e).draw km (mb j e)
    stage (((reweightsRep r,(D,keys.map index)),
        ((sourcePrepared rank parent w a ft fq,Numbered.set M.val),tableRep f)),
      List.ofFn (fun j=>
        (List.ofFn (fun i=>(List.ofFn (bits j i).1,localBitsRep (bits j i).2)),
          (List.ofFn (orderedEnum (BagEdge bags))).map (fun e=>(index e,List.ofFn (mb j e))))))=
      (TreeFraction.repr (Counting.ratioEstimate ((∑ i,scalarA s m i)/(S:ℚ))
        ((∑ i,scalarD s m r i)/(S:ℚ))),
       keys.map (fun e=>(index e,TreeFraction.repr (Counting.upperEstimate D
         ((∑ i,scalarD s m r i)/(S:ℚ)) ((∑ i,scalarProbe s m r e i)/(S:ℚ)))))) := by
  dsimp only
  unfold stage sampleMany
  dsimp only
  rw [List.map_ofFn]
  simp only [Function.comp_def,sample_source hbags hG rank parent hb hne hp ft fq hq w hw M a ha f]
  exact statistics_rep _ _ r hr D keys

end MatchingFPRAS.NumericMarking

end OAI
