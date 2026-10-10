import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeGeneratedUpdate
import OAI.Combinatorics.MatchingCount.Algorithm.TreeStageActivity

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

abbrev StageControls := ((List Bool×List Bool)×ℕ)×(List Bool×List Bool)
abbrev SparseStageData := ((GraphData×List Bool)×StageControls)×Vector
abbrev SparseStageInput := SparseStageData×List SampleBits

def currentActivityArg (x : SparseStageData) : ActivityData := (x.1.1,x.2)
def currentActivityArgRealizer : Realizer currentActivityArg :=
  (TreeTyped.pair (first (A:=(GraphData×List Bool)×StageControls) (B:=Vector)).fst second).congr (fun _=>rfl)
lemma polynomial_currentActivityArg : PolynomialTime currentActivityArgRealizer :=
  polynomial_congr _ (TreeTyped.polynomial_pair (polynomial_fst polynomial_first) polynomial_second)
def sparseCurrentMatrix (x : SparseStageData) : Matrix := stageMatrix (currentActivityArg x)
def sparseCurrentMatrixRealizer : Realizer sparseCurrentMatrix :=
  (composition currentActivityArgRealizer stageMatrixRealizer).congr (fun _=>rfl)
lemma polynomial_sparseCurrentMatrix : PolynomialTime sparseCurrentMatrixRealizer :=
  polynomial_congr _ (polynomial_composition polynomial_currentActivityArg polynomial_stageMatrix)

def nextActivityArg (x : SparseStageData) : ActivityData := ((x.1.1.1,false::x.1.1.2),x.2)
def nextActivityArgRealizer : Realizer nextActivityArg := (TreeTyped.pair
  (TreeTyped.pair first.fst.fst (composition (TreeTyped.pair (constant false) first.fst.snd) listCons)) second).congr (fun _=>rfl)
lemma polynomial_nextActivityArg : PolynomialTime nextActivityArgRealizer := by
  unfold nextActivityArgRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  tree_cost

def sparseNextMatrix (x : SparseStageData) : Matrix := stageMatrix (nextActivityArg x)
def sparseNextMatrixRealizer : Realizer sparseNextMatrix :=
  (composition nextActivityArgRealizer stageMatrixRealizer).congr (fun _=>rfl)
lemma polynomial_sparseNextMatrix : PolynomialTime sparseNextMatrixRealizer :=
  polynomial_congr _ (polynomial_composition polynomial_nextActivityArg polynomial_stageMatrix)

def sparseBagInput (x : SparseStageData) : BagBuildInput :=
  (((sparseCurrentMatrix x,x.1.2.1.1.1),x.1.1.1.1),x.1.2.1.1.2)
def sparseBagInputRealizer : Realizer sparseBagInput := (TreeTyped.pair
  (TreeTyped.pair (TreeTyped.pair sparseCurrentMatrixRealizer first.snd.fst.fst.fst) first.fst.fst.fst)
  first.snd.fst.fst.snd).congr (fun _=>rfl)
lemma polynomial_sparseBagInput : PolynomialTime sparseBagInputRealizer := by
  unfold sparseBagInputRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_sparseCurrentMatrix
  tree_cost

def sparseGeneratedInput (x : SparseStageData) : GeneratedInput :=
  ((sparseBagInput x,x.1.2.1.2),x.1.2.2)
def sparseGeneratedInputRealizer : Realizer sparseGeneratedInput := (TreeTyped.pair
  (TreeTyped.pair sparseBagInputRealizer first.snd.fst.snd) first.snd.snd).congr (fun _=>rfl)
lemma polynomial_sparseGeneratedInput : PolynomialTime sparseGeneratedInputRealizer := by
  unfold sparseGeneratedInputRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_sparseBagInput
  tree_cost

def sparseUpdateData (x : SparseStageData) : GeneratedUpdateData :=
  ((sparseGeneratedInput x,sparseNextMatrix x),x.2)
def sparseUpdateDataRealizer : Realizer sparseUpdateData :=
  (TreeTyped.pair (TreeTyped.pair sparseGeneratedInputRealizer sparseNextMatrixRealizer) second).congr (fun _=>rfl)
lemma polynomial_sparseUpdateData : PolynomialTime sparseUpdateDataRealizer :=
  polynomial_congr _ (TreeTyped.polynomial_pair (TreeTyped.polynomial_pair polynomial_sparseGeneratedInput polynomial_sparseNextMatrix)
    polynomial_second)

def sparseStage (x : SparseStageInput) : Fraction×Vector := generatedUpdate (sparseUpdateData x.1,x.2)
def sparseStageRealizer : Realizer sparseStage := (composition
  (TreeTyped.pair (composition (first (A:=SparseStageData) (B:=List SampleBits)) sparseUpdateDataRealizer) second)
  generatedUpdateRealizer).congr (fun _=>rfl)
lemma polynomial_sparseStage : PolynomialTime sparseStageRealizer := polynomial_congr _
  (polynomial_composition (TreeTyped.polynomial_pair (polynomial_composition polynomial_first polynomial_sparseUpdateData)
    polynomial_second) polynomial_generatedUpdate)

lemma sparseUpdateData_source {G : GraphInput} {j : ℕ} (s : FiniteTrial.ScaleState G j)
    (K D : ℕ) (ft fq : List Bool) :
    sparseUpdateData (((graphRep G,List.replicate j false),
      (((List.replicate (2*K+2) false,List.replicate (2*K) false),D),(ft,fq))),vectorRep s.scale)=
      (((((((matrixRep s.activity,List.replicate (2*K+2) false),List.range G.n),List.replicate (2*K) false),D),(ft,fq)),
       matrixRep s.nextActivity),vectorRep s.scale) := by
  unfold sparseUpdateData sparseGeneratedInput sparseBagInput sparseCurrentMatrix sparseNextMatrix currentActivityArg nextActivityArg
  dsimp only
  rw [stageMatrix_rep G _ s.scale (fun i=>(s.positive i).le),stageMatrix_rep G _ s.scale (fun i=>(s.positive i).le)]
  simp only [List.length_replicate,List.length_cons]
  rfl

lemma sparseStage_source {G : GraphInput} [Nontrivial (Fin G.n)] (hn : 2≤G.n)
    (he : Even G.n) {j : ℕ} (s : FiniteTrial.ScaleState G j) (K : ℕ)
    (hD : 0<FiniteTrial.sourceD (G:=G) K)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge s.activity a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {S k r km : ℕ}
    (bits : Fin S→Fin r→ScanBits (SourceVertex (Fin G.n) K) k)
    (mb : Fin S→BagEdge (RationalSource.bags s.activity K)→Fin km→Bool) :
    let x := fun i=>generatedSourceSample he s.activity s.activity_pos K
      (FiniteTrial.sourceD (G:=G) K) hD hu ft fq hq (bits i) (mb i)
    let keys := List.ofFn (orderedEnum (BagEdge (RationalSource.bags s.activity K)))
    sparseStage
      ((((graphRep G,List.replicate j false),
        (((List.replicate (2*K+2) false,List.replicate (2*K) false),FiniteTrial.sourceD (G:=G) K),(ft,fq))),vectorRep s.scale),
       List.ofFn (fun i=>(List.ofFn (fun z=>(List.ofFn (bits i z).1,localBitsRep (bits i z).2)),
         keys.map (fun e=>(index e,List.ofFn (mb i e))))))=
      (TreeFraction.repr (s.ratioEstimate x),vectorRep (s.update hn x).scale) := by
  dsimp only
  unfold sparseStage
  rw [sparseUpdateData_source]
  exact generatedUpdate_source hn he s K hD hu ft fq hq bits mb

open TreePost Turing

theorem sparseStage_post : ∃ p : Polynomial ℕ,∀ x : SparseStageInput,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine sparseStageRealizer.program) (packed x) coins).state=none ∧
      (run (machine sparseStageRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (sparseStage x)) :=
  polynomial_compiles sparseStageRealizer polynomial_sparseStage
end MatchingFPRAS.ExecutableSource

end OAI
