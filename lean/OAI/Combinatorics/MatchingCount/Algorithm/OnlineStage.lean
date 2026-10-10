import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TreeSparseStage
import OAI.Combinatorics.MatchingCount.Probability.OnlineSampleLaw

namespace OAI

namespace MatchingFPRAS.OnlineStage
open PhysicalStream TreeTyped ExecutableSource NumericLadder TreeFraction ExecutableScaling
open UnitRefresh Transport Enlargement TreeTyped.Numbered ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

abbrev Input := SparseStageData×(ℕ×OnlineSample.Request)
def execute (x : Input) : Experiment (Fraction×Vector) :=
  (OnlineSample.many x.2).map (fun bs=>sparseStage (x.1,bs))
noncomputable def executeRealizer : OnlineTree.Realizer execute :=
  (OnlineTree.composition (OnlineTree.pair (OnlineTree.deterministic TreeTyped.first)
    (OnlineTree.composition (OnlineTree.deterministic TreeTyped.second) OnlineSample.manyRealizer))
    (OnlineTree.deterministic sparseStageRealizer)).congr (by
      intro x h; simp only [execute,Experiment.mean_bind,Experiment.mean_map,Experiment.mean])

variable {G : GraphInput} [Nontrivial (Fin G.n)]
noncomputable def data {j : ℕ} (s : FiniteTrial.ScaleState G j) (K D : ℕ) (ft fq : List Bool) : SparseStageData :=
  (((graphRep G,List.replicate j false),
    (((List.replicate (2*K+2) false,List.replicate (2*K) false),D),(ft,fq))),vectorRep s.scale)

lemma source_mean (hn : 2≤G.n) (he : Even G.n) {j : ℕ} (s : FiniteTrial.ScaleState G j)
    (K : ℕ) (hD : 0<FiniteTrial.sourceD (G:=G) K)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge s.activity a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) (S k r km : ℕ)
    (h : Fraction×Vector → ℚ) :
    let E := BagEdge (RationalSource.bags s.activity K)
    let keys := fun i : Fin (Fintype.card E)=>index (orderedEnum E i)
    let req : OnlineSample.Request :=
      (((k,Fintype.card (SourceVertex (Fin G.n) K)),r),(km,List.ofFn keys))
    (execute (data s K (FiniteTrial.sourceD (G:=G) K) ft fq,(S,req))).mean h=
      qaverage (fun bs : Fin S→OnlineSample.Random (Fintype.card (SourceVertex (Fin G.n) K)) k r (Fintype.card E) km=>
        let x := fun i=>generatedSourceSample he s.activity s.activity_pos K
          (FiniteTrial.sourceD (G:=G) K) hD hu ft fq hq (bs i).1
          (fun e=>(bs i).2 ((orderedEnum E).symm e))
        h (repr (s.ratioEstimate x),vectorRep (s.update hn x).scale)) := by
  dsimp only
  rw [execute,Experiment.mean_map,OnlineSample.mean_many]
  apply qaverage_congr
  intro bs
  have hs:=sparseStage_source hn he s K hD hu ft fq hq (fun i=>(bs i).1)
    (fun i e=>(bs i).2 ((orderedEnum (BagEdge (RationalSource.bags s.activity K))).symm e))
  dsimp only at hs
  have rows : List.ofFn (fun i=>OnlineSample.sampleRep
        (fun e=>index (orderedEnum (BagEdge (RationalSource.bags s.activity K)) e)) (bs i)) =
      List.ofFn (fun i=>(List.ofFn (fun z=>(List.ofFn ((bs i).1 z).1,localBitsRep ((bs i).1 z).2)),
        (List.ofFn (orderedEnum (BagEdge (RationalSource.bags s.activity K)))).map
          (fun e=>(index e,List.ofFn ((bs i).2 ((orderedEnum _).symm e)))))) := by
    simp only [OnlineSample.sampleRep,OnlineSample.scanRep,OnlineSample.localRep,List.map_ofFn,
      Function.comp_def,Equiv.symm_apply_apply,localBitsRep]
  rw [rows]
  exact congrArg h hs
end MatchingFPRAS.OnlineStage

end OAI
