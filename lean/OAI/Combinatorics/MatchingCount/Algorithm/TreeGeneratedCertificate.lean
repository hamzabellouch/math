import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeGeneratedUpdate

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableMarking ExecutableStatistics

lemma numeric_observableD_rep {E : Type} [Fintype E] [LinearOrder E]
    (s : Finset E) (m : E→Fin 3) (r : E→ℚ) (hr : ∀ e,0≤r e) :
    ExecutableMarking.observableD reweight (reweightsRep r,numericMarks s m)=
      TreeFraction.repr (if ∀ e∈s,m e=0 then ∏ e∈s,r e else 0) := by
  rw [numericMarks_eq,observableD_rep reweight (reweightsRep r) (extend 1 r)
    (extend_nonneg r hr) (reweight_rep r)]
  apply congrArg TreeFraction.repr
  simpa only [scalarD] using scalarD_numbered (fun _ : Fin 1=>s) (fun _ : Fin 1=>m) r 0
end MatchingFPRAS.NumericMarking

namespace MatchingFPRAS.TreeTyped
variable {A B C : Type} [Codec A] [Codec B] [Codec C]
def applyFirst {f : A→C} (F : Realizer f) : Realizer (fun x : A×B=>f x.1) :=
  composition first F
lemma polynomial_applyFirst {f : A→C} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (applyFirst (B:=B) F) := polynomial_composition polynomial_first hF
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableMarking ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

abbrev GeneratedCertificateInput := GeneratedStageData×SampleBits
def generatedCertificate (x : GeneratedCertificateInput) : Fraction :=
  ExecutableMarking.observableD reweight (generatedReweights x.1,generatedMarked (x.1.1,x.2))
def certificateSampleArg (x : GeneratedCertificateInput) : GeneratedInput×SampleBits := (x.1.1,x.2)
def certificateSampleArgRealizer : Realizer certificateSampleArg :=
  (TreeTyped.pair (first (A:=GeneratedStageData) (B:=SampleBits)).fst second).congr (fun _=>rfl)
lemma polynomial_certificateSampleArg : PolynomialTime certificateSampleArgRealizer :=
  polynomial_congr _ (TreeTyped.polynomial_pair (polynomial_fst polynomial_first) polynomial_second)
def certificateSample (x : GeneratedCertificateInput) : ExecutableMarking.Marks ℕ := generatedMarked (certificateSampleArg x)
def certificateSampleRealizer : Realizer certificateSample :=
  (composition certificateSampleArgRealizer generatedMarkedRealizer).congr (fun _=>rfl)
lemma polynomial_certificateSample : PolynomialTime certificateSampleRealizer :=
  polynomial_congr _ (polynomial_composition polynomial_certificateSampleArg polynomial_generatedMarked)
def certificateReweights (x : GeneratedCertificateInput) : Reweights := generatedReweights x.1
def certificateReweightsRealizer : Realizer certificateReweights :=
  applyFirst (B:=SampleBits) generatedReweightsRealizer
lemma polynomial_certificateReweights : PolynomialTime certificateReweightsRealizer :=
  polynomial_applyFirst polynomial_generatedReweights
def certificateArgs (x : GeneratedCertificateInput) : Reweights×ExecutableMarking.Marks ℕ :=
  (certificateReweights x,certificateSample x)
def certificateArgsRealizer : Realizer certificateArgs :=
  (TreeTyped.pair certificateReweightsRealizer certificateSampleRealizer).congr (fun _=>rfl)
lemma polynomial_certificateArgs : PolynomialTime certificateArgsRealizer :=
  polynomial_congr _ (TreeTyped.polynomial_pair polynomial_certificateReweights polynomial_certificateSample)
def generatedCertificateRealizer : Realizer generatedCertificate :=
  (composition (f:=certificateArgs) (g:=ExecutableMarking.observableD reweight)
    certificateArgsRealizer (observableDRealizer reweightRealizer)).congr (fun _=>rfl)
lemma polynomial_generatedCertificate : PolynomialTime generatedCertificateRealizer :=
  polynomial_congr _ (polynomial_composition polynomial_certificateArgs (polynomial_observableD polynomial_reweight))

lemma numeric_certificate_source {n : ℕ} [Nontrivial (Fin n)]
    (w w₁ : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (hw₁ : ∀ a b,0≤w₁ a b)
    (K : ℕ) (x : RationalSource.Marked w K) :
    ExecutableMarking.observableD reweight (reweightsRep (RationalSource.bagReweight w w₁ K),
      numericMarks x.1.val (selectedMarks x.1.val x.2))=
      TreeFraction.repr (RationalSource.observableD w w₁ K x) := by
  rw [numeric_observableD_rep _ _ _ (reweight_nonneg w w₁ hw hw₁ K)]
  apply congrArg TreeFraction.repr
  unfold RationalSource.observableD
  simp only [selectedMarks_eq]

lemma generatedCertificate_source {n : ℕ} [Nontrivial (Fin n)]
    (hn : 2≤n) (he : Even n) (w w₁ : Fin n→Fin n→ℚ)
    (hw : ∀ a b,0<w a b) (hw₁ : ∀ a b,0≤w₁ a b) (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : BagEdge (RationalSource.bags w K)→Fin km→Bool) :
    generatedCertificate
      (((((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),(ft,fq)),matrixRep w₁),
       (List.ofFn (fun z=>(List.ofFn (bits z).1,localBitsRep (bits z).2)),
         (List.ofFn (orderedEnum (BagEdge (RationalSource.bags w K)))).map (fun e=>(index e,List.ofFn (mb e)))))=
      TreeFraction.repr (RationalSource.observableD w w₁ K
        (generatedSourceSample he w hw K D hD hu ft fq hq bits mb)) := by
  unfold generatedCertificate generatedReweights
  dsimp only
  rw [sourceReweights_source hn w w₁ (fun a b=>(hw a b).le) hw₁ K,
    generatedMarked_sourceSample hn he w hw K D hD hu ft fq hq bits mb]
  exact numeric_certificate_source w w₁ (fun a b=>(hw a b).le) hw₁ K _

open TreePost Turing

theorem generatedCertificate_post : ∃ p : Polynomial ℕ,∀ x : GeneratedCertificateInput,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine generatedCertificateRealizer.program) (packed x) coins).state=none ∧
      (run (machine generatedCertificateRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (generatedCertificate x)) :=
  polynomial_compiles generatedCertificateRealizer polynomial_generatedCertificate
end MatchingFPRAS.ExecutableSource

end OAI
