import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TreeSparseStage
import OAI.Combinatorics.MatchingCount.Algorithm.TreeGeneratedCertificate
import OAI.Combinatorics.MatchingCount.Algorithm.TreeCertificate

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

abbrev CertificateMatrixInput := GraphData×Vector
def certificateCellData (x : CertificateMatrixInput) : CellData := ((x.1.2,(0,1)),x.2)
def certificateCellDataRealizer : Realizer certificateCellData :=
  (TreeTyped.pair (TreeTyped.pair first.snd (constant (0,1))) second).congr (fun _=>rfl)
lemma polynomial_certificateCellData : PolynomialTime certificateCellDataRealizer := by
  unfold certificateCellDataRealizer; apply polynomial_congr
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def certificateMatrix (x : CertificateMatrixInput) : Matrix :=
  x.1.1.map (fun i=>stageRow ((certificateCellData x,x.1.1),i))
def certificateMatrixRealizer : Realizer certificateMatrix :=
  (composition (TreeTyped.pair (TreeTyped.pair certificateCellDataRealizer first.fst) first.fst)
    (mapWith stageRowRealizer)).congr (fun _=>rfl)
lemma polynomial_certificateMatrix : PolynomialTime certificateMatrixRealizer := by
  unfold certificateMatrixRealizer; apply polynomial_congr
  have := polynomial_certificateCellData
  have := polynomial_stageRow
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

lemma certificateMatrix_source {G : GraphInput} {j : ℕ} (s : FiniteTrial.ScaleState G j) :
    certificateMatrix (graphRep G,vectorRep s.scale)=matrixRep s.certificateActivity := by
  have hr (i j : Fin G.n) : (0:ℚ)≤ if (min i j,max i j)∈G.edges then 1 else 0 := by
    split_ifs <;> norm_num
  have hc (i j : Fin G.n) :
      rawCell (certificateCellData (graphRep G,vectorRep s.scale),(i.val,j.val))=
        TreeFraction.repr (if (min i j,max i j)∈G.edges then (1:ℚ) else 0) := by
    unfold rawCell certificateCellData
    dsimp only
    simp only [edge_mem_graphRep]
    split_ifs <;> rfl
  unfold certificateMatrix stageRow matrixRep
  change (List.range G.n).map _=List.ofFn _
  rw [ExecutableDP.map_range_ofFn]
  congr 1
  funext i
  change (List.range G.n).map _=List.ofFn _
  rw [ExecutableDP.map_range_ofFn]
  congr 1
  funext j
  unfold stageCell
  rw [hc,show (certificateCellData (graphRep G,vectorRep s.scale)).2=vectorRep s.scale from rfl,
    lookup_vectorRep s.scale i,lookup_vectorRep s.scale j,mul_repr (hr i j) (s.positive i).le,
    mul_repr (mul_nonneg (hr i j) (s.positive i).le) (s.positive j).le]
  rfl

def sparseCertificateMatrixArg (x : SparseStageData) : CertificateMatrixInput := (x.1.1.1,x.2)
def sparseCertificateMatrixArgRealizer : Realizer sparseCertificateMatrixArg :=
  (TreeTyped.pair first.fst.fst second).congr (fun _=>rfl)
lemma polynomial_sparseCertificateMatrixArg : PolynomialTime sparseCertificateMatrixArgRealizer := by
  unfold sparseCertificateMatrixArgRealizer; apply polynomial_congr
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost

def sparseCertificateData (x : SparseStageData) : GeneratedStageData :=
  (sparseGeneratedInput x,certificateMatrix (sparseCertificateMatrixArg x))
def sparseCertificateDataRealizer : Realizer sparseCertificateData := (TreeTyped.pair
  sparseGeneratedInputRealizer (composition sparseCertificateMatrixArgRealizer certificateMatrixRealizer)).congr (fun _=>rfl)
lemma polynomial_sparseCertificateData : PolynomialTime sparseCertificateDataRealizer := polynomial_congr _
  (TreeTyped.polynomial_pair polynomial_sparseGeneratedInput
    (polynomial_composition polynomial_sparseCertificateMatrixArg polynomial_certificateMatrix))

def sparseCertificate (x : SparseStageData×SampleBits) : Fraction := generatedCertificate (sparseCertificateData x.1,x.2)
def sparseCertificateRealizer : Realizer sparseCertificate := (composition
  (TreeTyped.pair (composition first sparseCertificateDataRealizer) second) generatedCertificateRealizer).congr (fun _=>rfl)
lemma polynomial_sparseCertificate : PolynomialTime sparseCertificateRealizer := polynomial_congr _
  (polynomial_composition (TreeTyped.polynomial_pair
    (polynomial_composition polynomial_first polynomial_sparseCertificateData) polynomial_second) polynomial_generatedCertificate)

lemma sparseCertificateData_source {G : GraphInput} {j : ℕ} (s : FiniteTrial.ScaleState G j)
    (K D : ℕ) (ft fq : List Bool) :
    sparseCertificateData (((graphRep G,List.replicate j false),
      (((List.replicate (2*K+2) false,List.replicate (2*K) false),D),(ft,fq))),vectorRep s.scale)=
      ((((((matrixRep s.activity,List.replicate (2*K+2) false),List.range G.n),List.replicate (2*K) false),D),(ft,fq)),
       matrixRep s.certificateActivity) := by
  unfold sparseCertificateData sparseGeneratedInput sparseBagInput sparseCurrentMatrix currentActivityArg sparseCertificateMatrixArg
  dsimp only
  rw [stageMatrix_rep G _ s.scale (fun i=>(s.positive i).le),certificateMatrix_source]
  simp only [List.length_replicate]
  rfl

lemma sparseCertificate_source {G : GraphInput} [Nontrivial (Fin G.n)] (hn : 2≤G.n)
    (he : Even G.n) {j : ℕ} (s : FiniteTrial.ScaleState G j) (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge s.activity a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin G.n) K) k)
    (mb : BagEdge (RationalSource.bags s.activity K)→Fin km→Bool) :
    let keys := List.ofFn (orderedEnum (BagEdge (RationalSource.bags s.activity K)))
    sparseCertificate
      ((((graphRep G,List.replicate j false),
        (((List.replicate (2*K+2) false,List.replicate (2*K) false),D),(ft,fq))),vectorRep s.scale),
       (List.ofFn (fun z=>(List.ofFn (bits z).1,localBitsRep (bits z).2)),
         keys.map (fun e=>(index e,List.ofFn (mb e)))))=
      TreeFraction.repr (RationalSource.observableD s.activity s.certificateActivity K
        (generatedSourceSample he s.activity s.activity_pos K D hD hu ft fq hq bits mb)) := by
  dsimp only
  unfold sparseCertificate
  rw [sparseCertificateData_source]
  have hnonneg : ∀ a b,0 ≤ s.certificateActivity a b := by
    intro a b
    have h:=s.toReal.certificateActivity_nonneg a b
    rw [←s.certificateActivity_cast] at h
    change (0:ℝ) ≤ (s.certificateActivity a b:ℝ) at h
    exact_mod_cast h
  exact generatedCertificate_source hn he s.activity s.certificateActivity s.activity_pos hnonneg K D hD hu ft fq hq bits mb

lemma sparseCertificate_zero {G : GraphInput} [Nontrivial (Fin G.n)] (hn : 2≤G.n)
    (he : Even G.n) {j : ℕ} (s : FiniteTrial.ScaleState G j) (hZ : Z G=0)
    (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge s.activity a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin G.n) K) k)
    (mb : BagEdge (RationalSource.bags s.activity K)→Fin km→Bool) :
    let keys := List.ofFn (orderedEnum (BagEdge (RationalSource.bags s.activity K)))
    sparseCertificate
      ((((graphRep G,List.replicate j false),
        (((List.replicate (2*K+2) false,List.replicate (2*K) false),D),(ft,fq))),vectorRep s.scale),
       (List.ofFn (fun z=>(List.ofFn (bits z).1,localBitsRep (bits z).2)),
         keys.map (fun e=>(index e,List.ofFn (mb e)))))=TreeFraction.repr 0 := by
  dsimp only
  rw [sparseCertificate_source hn he s K D hD hu ft fq hq bits mb,
    generated_certificate_zero he s hZ K D hD hu ft fq hq bits mb]

open TreePost Turing

theorem sparseCertificate_post : ∃ p : Polynomial ℕ,∀ x : SparseStageData×SampleBits,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine sparseCertificateRealizer.program) (packed x) coins).state=none ∧
      (run (machine sparseCertificateRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (sparseCertificate x)) :=
  polynomial_compiles sparseCertificateRealizer polynomial_sparseCertificate
end MatchingFPRAS.ExecutableSource

end OAI
