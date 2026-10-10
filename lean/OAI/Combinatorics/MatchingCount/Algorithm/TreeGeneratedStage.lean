import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeGeneratedMarked
import OAI.Combinatorics.MatchingCount.Algorithm.TreeReweightTable
import OAI.Combinatorics.MatchingCount.Algorithm.TreeNumericStage
import OAI.Combinatorics.MatchingCount.Algorithm.TreeStatistics

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

def tableIndex (x : BagBuildInput×Key) : ℕ := (sourceTables x.1).1.idxOf x.2
def tableIndexRealizer : Realizer tableIndex := keyLookup second
  (composition (first (A:=BagBuildInput) (B:=Key)) sourceTablesRealizer).fst
lemma polynomial_tableIndex : PolynomialTime tableIndexRealizer :=
  polynomial_keyLookup polynomial_second
    (polynomial_fst (polynomial_composition polynomial_first polynomial_sourceTables))
def sourceAllIndices (x : BagBuildInput) : List ℕ :=
  (sourceTables x).1.map (fun key=>tableIndex (x,key))
def sourceAllIndicesRealizer : Realizer sourceAllIndices := rowsWith tableIndexRealizer sourceTablesRealizer.fst
lemma polynomial_sourceAllIndices : PolynomialTime sourceAllIndicesRealizer :=
  polynomial_rowsWith polynomial_tableIndex (polynomial_fst polynomial_sourceTables)
lemma sourceAllIndices_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    sourceAllIndices (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      (List.ofFn (orderedEnum (BagEdge (RationalSource.bags w K)))).map index := by
  unfold sourceAllIndices
  rw [sourceTables_catalog hn w hw K]
  unfold sourceCatalog
  rw [List.map_ofFn,List.map_ofFn]
  congr 1
  funext i
  dsimp only [Function.comp_apply,tableIndex]
  rw [sourceTables_catalog hn w hw K,sourceCatalog_index]

abbrev GeneratedStageData := GeneratedInput×Matrix
abbrev GeneratedStageInput := GeneratedStageData×List SampleBits
def generatedObservables (x : GeneratedStageData) : Reweights×(ℕ×List ℕ) :=
  (sourceReweights (x.1.1.1,x.2),(x.1.1.2,sourceAllIndices x.1.1.1))
def generatedReweightArg : Realizer (fun x : GeneratedStageData=>(x.1.1.1,x.2)) :=
  (pair (first (A:=GeneratedInput) (B:=Matrix)).fst.fst second).congr (fun _=>rfl)
lemma polynomial_generatedReweightArg : PolynomialTime generatedReweightArg := by
  unfold generatedReweightArg
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  tree_cost

def generatedReweights (x : GeneratedStageData) : Reweights := sourceReweights (x.1.1.1,x.2)
def generatedReweightsRealizer : Realizer generatedReweights :=
  (composition generatedReweightArg sourceReweightsRealizer).congr (fun _=>rfl)
lemma polynomial_generatedReweights : PolynomialTime generatedReweightsRealizer :=
  polynomial_congr _ (polynomial_composition polynomial_generatedReweightArg polynomial_sourceReweights)

def generatedIndexData (x : GeneratedStageData) : ℕ×List ℕ :=
  (x.1.1.2,sourceAllIndices x.1.1.1)
def generatedIndexDataRealizer : Realizer generatedIndexData := (pair
  (first (A:=GeneratedInput) (B:=Matrix)).fst.snd
  (composition (first (A:=GeneratedInput) (B:=Matrix)).fst.fst sourceAllIndicesRealizer)).congr (fun _=>rfl)
lemma polynomial_generatedIndexData : PolynomialTime generatedIndexDataRealizer := by
  unfold generatedIndexDataRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_sourceAllIndices
  tree_cost

def generatedObservablesRealizer : Realizer generatedObservables :=
  (TreeTyped.pair generatedReweightsRealizer generatedIndexDataRealizer).congr (fun _=>rfl)
lemma polynomial_generatedObservables : PolynomialTime generatedObservablesRealizer :=
  polynomial_congr _ (TreeTyped.polynomial_pair polynomial_generatedReweights polynomial_generatedIndexData)

def generatedStageSetup (x : GeneratedStageData) : (Reweights×(ℕ×List ℕ))×SampleContext :=
  (generatedObservables x,generatedContext x.1)
def generatedStageSetupRealizer : Realizer generatedStageSetup := (pair generatedObservablesRealizer
  (composition first generatedContextRealizer)).congr (fun _=>rfl)
lemma polynomial_generatedStageSetup : PolynomialTime generatedStageSetupRealizer :=
  polynomial_congr _ (TreeTyped.polynomial_pair polynomial_generatedObservables (polynomial_composition polynomial_first polynomial_generatedContext))

def stageWith {A : Type} [Codec A] {f : A→(Reweights×(ℕ×List ℕ))×SampleContext}
    (F : Realizer f) : Realizer (fun x : A×List SampleBits=>stage (f x.1,x.2)) :=
  (composition (pair (composition (first (A:=A) (B:=List SampleBits)) F) second) stageRealizer).congr (fun _=>rfl)
lemma polynomial_stageWith {A : Type} [Codec A] {f : A→(Reweights×(ℕ×List ℕ))×SampleContext}
    {F : Realizer f} (hF : PolynomialTime F) : PolynomialTime (stageWith F) :=
  polynomial_congr _ (polynomial_composition (TreeTyped.polynomial_pair (polynomial_composition polynomial_first hF) polynomial_second)
    polynomial_stage)

def generatedStage (x : GeneratedStageInput) : Fraction×List (ℕ×Fraction) :=
  stage (generatedStageSetup x.1,x.2)
def generatedStageRealizer : Realizer generatedStage := stageWith generatedStageSetupRealizer
lemma polynomial_generatedStage : PolynomialTime generatedStageRealizer :=
  polynomial_stageWith polynomial_generatedStageSetup

lemma generatedStage_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (he : Even n)
    (w w₁ : Fin n→Fin n→ℚ) (hw : ∀ a b,0<w a b) (hw₁ : ∀ a b,0≤w₁ a b)
    (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {S k r km : ℕ}
    (bits : Fin S→Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : Fin S→BagEdge (RationalSource.bags w K)→Fin km→Bool) :
    let s := fun j=>(ladderRun (RationalSource.bags_adjacent w K hu) (RationalSource.tree_acyclic w K)
        (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
        (RationalSource.bags_ranked w K hu) (RationalSource.bags_nonempty w K)
        (RationalSource.parent_rank w K) hq (RationalSource.bagWeight w K D)
        (RationalSource.startMatching w K he) k r (fun _=>RationalSource.startMatching w K he) (bits j)
        (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length)))).val
    let m := fun j e=>(RationalSource.markingTable w hw K D hD e).draw km (mb j e)
    let keys := List.ofFn (orderedEnum (BagEdge (RationalSource.bags w K)))
    generatedStage
      (((((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),(ft,fq)),matrixRep w₁),
       List.ofFn (fun j=>(List.ofFn (fun i=>(List.ofFn (bits j i).1,localBitsRep (bits j i).2)),
         keys.map (fun e=>(index e,List.ofFn (mb j e))))))=
      (TreeFraction.repr (Counting.ratioEstimate ((∑ i,scalarA s m i)/(S:ℚ))
        ((∑ i,scalarD s m (RationalSource.bagReweight w w₁ K) i)/(S:ℚ))),
       keys.map (fun e=>(index e,TreeFraction.repr (Counting.upperEstimate D
         ((∑ i,scalarD s m (RationalSource.bagReweight w w₁ K) i)/(S:ℚ))
         ((∑ i,scalarProbe s m (RationalSource.bagReweight w w₁ K) e i)/(S:ℚ)))))) := by
  dsimp only
  unfold generatedStage generatedStageSetup generatedObservables generatedContext
  dsimp only
  rw [sourceReweights_source hn w w₁ (fun a b=>(hw a b).le) hw₁ K,
    sourceAllIndices_source hn w (fun a b=>(hw a b).le) K,
    generatedPrepared_source hn w (fun a b=>(hw a b).le) K D ft fq,
    exactStart_source hn he w (fun a b=>(hw a b).le) K,sourceMarks_source hn w hw K D hD]
  exact stage_source (RationalSource.bags_adjacent w K hu) (RationalSource.tree_acyclic w K)
    (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
    (RationalSource.bags_ranked w K hu) (RationalSource.bags_nonempty w K)
    (RationalSource.parent_rank w K) ft fq hq (RationalSource.bagWeight w K D)
    (bagWeight_nonneg w hw K D) (RationalSource.startMatching w K he) _
    (setupBags_source hn w (fun a b=>(hw a b).le) K) _ _
    (reweight_nonneg w w₁ (fun a b=>(hw a b).le) hw₁ K) D _ bits mb

open TreePost Turing

theorem generatedStage_post : ∃ p : Polynomial ℕ,∀ x : GeneratedStageInput,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine generatedStageRealizer.program) (packed x) coins).state=none ∧
      (run (machine generatedStageRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (generatedStage x)) :=
  polynomial_compiles generatedStageRealizer polynomial_generatedStage
end MatchingFPRAS.ExecutableSource

end OAI
