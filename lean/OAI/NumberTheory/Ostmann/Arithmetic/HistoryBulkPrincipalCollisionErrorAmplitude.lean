import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitudeProduct
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitudeSource

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError
open Construction Conclusion Filter HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkGiantCorrectedBounds
open HistoryBulkSelectedPrincipalAmplitude HistorySelectedPairDerivativeBounds
open HistoryBulkSelectedIntegralReplacement HistoryBulkReplacementGeometry
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

structure PrincipalAmplitudeData (C : InitialSourceChoice d Bs BD Bz k L E)
    (outside : List ℕ) (l : ℕ) where
  left : History l
  right : History l
  leftSupported : left.Supported (frequencyBound Bs BD Bz k L) outside
  rightSupported : right.Supported (frequencyBound Bs BD Bz k L) outside
  leftLabels : TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) left
  rightLabels : TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) right
  rootMatching : RootMatching left right
  leftSource : SourceBounds (bulkSize k L/2) k C.giantCenter (C.cells.center (bulkSize k L/2))
    left (leftMap left right) (giantCoordinates left right) (pairBackground left right)
    (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1)
  rightSource : SourceBounds (bulkSize k L/2) k C.giantCenter (C.cells.center (bulkSize k L/2))
    right (rightMap left right) (giantCoordinates left right) (pairBackground left right)
    (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1)
  s : ℕ
  outsideLength : outside.length = 2*s
  outsidePrime : ∀ q ∈ outside, q.Prime
  outsideFrequency : ∀ q ∈ outside, ∀ j ≤ l, frequencyBound Bs BD Bz k L j < q
  primeEquiv : Bool ≃ giantCoordinates left right
  mixedEquiv : Option Unit ≃ giantCoordinates left right
  bulkEquiv : (Fin (2^l) × Fin (2*(bulkSize k L/2))) ≃ bulkCoordinates left right
  permutation : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))
  K : ℕ
  residue : Fin (2^l) × Fin (2*(bulkSize k L/2)) →
    (ZMod (bulkModulus left right outside K))ˣ
  independent : Bool

namespace PrincipalAmplitudeData
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ} {l : ℕ}

def value (P : PrincipalAmplitudeData C outside l) (corrected mixed : Bool)
    (u : (Fin (2^l) × Fin (2*(bulkSize k L/2))) → C.bulk.Sample) : ℂ :=
  rootTest P.independent mixed d P.left P.right P.leftSupported P.rightSupported
    P.outsidePrime P.outsideFrequency P.permutation P.K P.residue *
  if corrected then
    if mixed then
      mixedGiantScalar C.giantCenter (Construction.logCellMass C.giantCenter ∅)
        (jointCorrectedScalar C P.s P.left P.right P.leftSupported P.rightSupported
          P.mixedEquiv P.bulkEquiv) (fun i => ((u i).val : ℝ))
    else
      primeGiantScalar C.giantCenter (Construction.logCellMass C.giantCenter ∅)
        (jointCorrectedScalar C P.s P.left P.right P.leftSupported P.rightSupported
          P.primeEquiv P.bulkEquiv) (fun i => ((u i).val : ℝ))
  else
    if mixed then
      mixedGiantScalar C.giantCenter (Construction.logCellMass C.giantCenter ∅)
        (jointScalar C P.s P.left P.right P.leftSupported P.rightSupported
          P.mixedEquiv P.bulkEquiv) (fun i => ((u i).val : ℝ))
    else
      primeGiantScalar C.giantCenter (Construction.logCellMass C.giantCenter ∅)
        (jointScalar C P.s P.left P.right P.leftSupported P.rightSupported
          P.primeEquiv P.bulkEquiv) (fun i => ((u i).val : ℝ))

end PrincipalAmplitudeData

theorem selected_principalAmplitudeData_norm_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hBs : 0 ≤ Bs) (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      ∀ (outside : List ℕ) (l : ℕ) (P : PrincipalAmplitudeData C outside l)
        (corrected mixed : Bool),
      (if corrected then l < k else l ≤ k) →
      ∀ u : (Fin (2^l) × Fin (2*(bulkSize k L/2))) → C.bulk.Sample,
      ‖P.value corrected mixed u‖ ≤ (outside.prod : ℝ)^(2^(l+1)) *
        Real.exp ((selectedExponent Bs BD Bz k+64)*((bulkSize k L : ℝ)+1)) := by
  filter_upwards [source_corrected_giantScalar_eventually d Bs BD Bz hBs hk,
    source_plain_giantScalar_eventually d Bs BD Bz hBs hk] with L hcorrected hplain
  intro E C hblock hcenter outside l P corrected mixed hl u
  have hpos : ∀ q ∈ outside, 0 < q := fun q hq => (P.outsidePrime q hq).pos
  cases corrected with
  | false =>
    have hscalar := hplain E C hblock hcenter P.s hpos P.outsideLength l
      P.left P.right P.leftSupported P.rightSupported hl P.leftLabels P.rightLabels
      P.rootMatching P.leftSource P.rightSource P.primeEquiv P.mixedEquiv P.bulkEquiv u
    cases mixed
    · exact norm_rootTest_mul_le P.independent false d P.left P.right
        P.leftSupported P.rightSupported P.outsidePrime P.outsideFrequency
        P.permutation P.K P.residue (bulkSize k L) (selectedExponent Bs BD Bz k) _ hscalar.1
    · exact norm_rootTest_mul_le P.independent true d P.left P.right
        P.leftSupported P.rightSupported P.outsidePrime P.outsideFrequency
        P.permutation P.K P.residue (bulkSize k L) (selectedExponent Bs BD Bz k) _ hscalar.2
  | true =>
    have hscalar := hcorrected E C hblock hcenter P.s hpos P.outsideLength l
      P.left P.right P.leftSupported P.rightSupported hl P.leftLabels P.rightLabels
      P.rootMatching P.leftSource P.rightSource P.primeEquiv P.mixedEquiv P.bulkEquiv u
    cases mixed
    · exact norm_rootTest_mul_le P.independent false d P.left P.right
        P.leftSupported P.rightSupported P.outsidePrime P.outsideFrequency
        P.permutation P.K P.residue (bulkSize k L) (selectedExponent Bs BD Bz k) _ hscalar.1
    · exact norm_rootTest_mul_le P.independent true d P.left P.right
        P.leftSupported P.rightSupported P.outsidePrime P.outsideFrequency
        P.permutation P.K P.residue (bulkSize k L) (selectedExponent Bs BD Bz k) _ hscalar.2

end Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError

end

end OAI
