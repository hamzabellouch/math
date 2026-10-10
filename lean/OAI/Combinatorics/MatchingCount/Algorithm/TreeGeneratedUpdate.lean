import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeBindings

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

abbrev GeneratedUpdateData := GeneratedStageData×Vector
abbrev GeneratedUpdateInput := GeneratedUpdateData×List SampleBits

def generatedUpdateArg : Realizer (fun x : GeneratedUpdateData=>(x.1.1.1,x.2)) :=
  (TreeTyped.pair (first (A:=GeneratedStageData) (B:=Vector)).fst.fst second).congr (fun _=>rfl)
lemma polynomial_generatedUpdateArg : PolynomialTime generatedUpdateArg := by
  unfold generatedUpdateArg
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  tree_cost

def generatedUpdateSetup (x : GeneratedUpdateData) : UpdateConfig×((Reweights×(ℕ×List ℕ))×SampleContext) :=
  (generatedUpdateConfig (x.1.1.1,x.2),generatedStageSetup x.1)
def generatedUpdateSetupRealizer : Realizer generatedUpdateSetup := (TreeTyped.pair
  (composition generatedUpdateArg generatedUpdateConfigRealizer)
  (composition (first (A:=GeneratedStageData) (B:=Vector)) generatedStageSetupRealizer)).congr (fun _=>rfl)
lemma polynomial_generatedUpdateSetup : PolynomialTime generatedUpdateSetupRealizer :=
  polynomial_congr _ (TreeTyped.polynomial_pair
    (polynomial_composition polynomial_generatedUpdateArg polynomial_generatedUpdateConfig)
    (polynomial_composition polynomial_first polynomial_generatedStageSetup))

def updateWith {A : Type} [Codec A]
    {f : A→UpdateConfig×((Reweights×(ℕ×List ℕ))×SampleContext)} (F : Realizer f) :
    Realizer (fun x : A×List SampleBits=>stageUpdate ((f x.1).1,((f x.1).2,x.2))) :=
  (composition (TreeTyped.pair (composition (first (A:=A) (B:=List SampleBits)) F) second)
    ((composition (TreeTyped.pair first.fst (TreeTyped.pair first.snd second)) stageUpdateRealizer))).congr (fun _=>rfl)
lemma polynomial_updateWith {A : Type} [Codec A]
    {f : A→UpdateConfig×((Reweights×(ℕ×List ℕ))×SampleContext)}
    {F : Realizer f} (hF : PolynomialTime F) : PolynomialTime (updateWith F) := by
  unfold updateWith
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_stageUpdate
  tree_cost

def generatedUpdate (x : GeneratedUpdateInput) : Fraction×Vector :=
  stageUpdate ((generatedUpdateSetup x.1).1,((generatedUpdateSetup x.1).2,x.2))
def generatedUpdateRealizer : Realizer generatedUpdate := updateWith generatedUpdateSetupRealizer
lemma polynomial_generatedUpdate : PolynomialTime generatedUpdateRealizer :=
  polynomial_updateWith polynomial_generatedUpdateSetup

variable {n : ℕ} [Nontrivial (Fin n)]
noncomputable def generatedSourceSample (he : Even n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ a b,0<w a b) (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : BagEdge (RationalSource.bags w K)→Fin km→Bool) : RationalSource.Marked w K :=
  TableMarking.reveal (BagEdge.Incident (bags:=RationalSource.bags w K))
    (ladderRun (RationalSource.bags_adjacent w K hu) (RationalSource.tree_acyclic w K)
      (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
      (RationalSource.bags_ranked w K hu) (RationalSource.bags_nonempty w K)
      (RationalSource.parent_rank w K) hq (RationalSource.bagWeight w K D)
      (RationalSource.startMatching w K he) k r (fun _=>RationalSource.startMatching w K he) bits
      (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length))))
    (fun e=>(RationalSource.markingTable w hw K D hD e).draw km (mb e))

lemma numericMarks_selected {E : Type} [Fintype E] [LinearOrder E]
    (s : Finset E) (m : E→Fin 3) (de : DecidableEq E) :
    numericMarks s (@selectedMarks E de s (fun e=>m e.val))=numericMarks s m := by
  unfold numericMarks
  apply List.map_congr_left
  intro e he
  have hm : e∈s := (Finset.mem_sort _).mp he
  simp only [selectedMarks,hm,↓reduceDIte]

lemma generatedMarked_sourceSample (hn : 2≤n) (he : Even n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ a b,0<w a b) (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : BagEdge (RationalSource.bags w K)→Fin km→Bool) :
    let x := generatedSourceSample he w hw K D hD hu ft fq hq bits mb
    generatedMarked
      ((((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),(ft,fq)),
       (List.ofFn (fun z=>(List.ofFn (bits z).1,localBitsRep (bits z).2)),
         (List.ofFn (orderedEnum (BagEdge (RationalSource.bags w K)))).map (fun e=>(index e,List.ofFn (mb e)))))=
      numericMarks x.1.val (selectedMarks x.1.val x.2) := by
  dsimp only
  rw [generatedMarked_source hn he w hw K D hD hu ft fq hq bits mb]
  dsimp only [generatedSourceSample,TableMarking.reveal]
  exact (numericMarks_selected (E:=BagEdge (RationalSource.bags w K)) _ _ _).symm

lemma generatedSamples_source (hn : 2≤n) (he : Even n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ a b,0<w a b) (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {S k r km : ℕ}
    (bits : Fin S→Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : Fin S→BagEdge (RationalSource.bags w K)→Fin km→Bool) :
    sampleMany
      (generatedContext (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),(ft,fq)),
       List.ofFn (fun i=>(List.ofFn (fun z=>(List.ofFn (bits i z).1,localBitsRep (bits i z).2)),
         (List.ofFn (orderedEnum (BagEdge (RationalSource.bags w K)))).map (fun e=>(index e,List.ofFn (mb i e))))))=
      sourceSamples w K (fun i=>generatedSourceSample he w hw K D hD hu ft fq hq (bits i) (mb i)) := by
  unfold sampleMany sourceSamples
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  have hm := generatedMarked_sourceSample hn he w hw K D hD hu ft fq hq (bits i) (mb i)
  simpa only [generatedMarked,Function.comp_def] using hm

lemma generatedUpdate_source {G : GraphInput} [Nontrivial (Fin G.n)] (hn : 2≤G.n)
    (he : Even G.n) {j : ℕ} (s : FiniteTrial.ScaleState G j) (K : ℕ)
    (hD : 0<FiniteTrial.sourceD (G:=G) K)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge s.activity a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {S k r km : ℕ}
    (bits : Fin S→Fin r→ScanBits (SourceVertex (Fin G.n) K) k)
    (mb : Fin S→BagEdge (RationalSource.bags s.activity K)→Fin km→Bool) :
    let x := fun i=>generatedSourceSample he s.activity s.activity_pos K
      (FiniteTrial.sourceD (G:=G) K) hD hu ft fq hq (bits i) (mb i)
    let keys := List.ofFn (orderedEnum (BagEdge (RationalSource.bags s.activity K)))
    generatedUpdate
      ((((((((matrixRep s.activity,List.replicate (2*K+2) false),List.range G.n),List.replicate (2*K) false),
        FiniteTrial.sourceD (G:=G) K),(ft,fq)),matrixRep s.nextActivity),vectorRep s.scale),
       List.ofFn (fun i=>(List.ofFn (fun z=>(List.ofFn (bits i z).1,localBitsRep (bits i z).2)),
         keys.map (fun e=>(index e,List.ofFn (mb i e))))))=
      (TreeFraction.repr (s.ratioEstimate x),vectorRep (s.update hn x).scale) := by
  dsimp only
  let x := fun i=>generatedSourceSample he s.activity s.activity_pos K
    (FiniteTrial.sourceD (G:=G) K) hD hu ft fq hq (bits i) (mb i)
  unfold generatedUpdate generatedUpdateSetup
  rw [generatedUpdateConfig_source hn s K]
  unfold stageUpdate generatedStageSetup
  dsimp only
  rw [generatedSamples_source hn he s.activity s.activity_pos K (FiniteTrial.sourceD (G:=G) K) hD hu ft fq hq bits mb]
  unfold generatedObservables
  dsimp only
  rw [sourceReweights_source hn s.activity s.nextActivity (fun a b=>(s.activity_pos a b).le)
      (fun a b=>(s.nextActivity_pos a b).le) K,
    sourceAllIndices_source hn s.activity (fun a b=>(s.activity_pos a b).le) K]
  exact scaleState_update_rep hn s x

open TreePost Turing

theorem generatedUpdate_post : ∃ p : Polynomial ℕ,∀ x : GeneratedUpdateInput,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine generatedUpdateRealizer.program) (packed x) coins).state=none ∧
      (run (machine generatedUpdateRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (generatedUpdate x)) :=
  polynomial_compiles generatedUpdateRealizer polynomial_generatedUpdate
end MatchingFPRAS.ExecutableSource

end OAI
