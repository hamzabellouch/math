import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreSourceMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacementPlainPrimeReferenceError

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators ContDiff
namespace Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacement
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryBulkSelectedIntegralReplacement
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkIntegralReplacement
open HistoryBulkGiantCorrectedBounds HistoryGiantXiReplacementActual HistoryGiantReferenceSourceBounds
open HistoryGiantReferenceMean HistorySignedXiTransport HistorySelectedPairDerivativeBounds PrimeCellFreezing
open HistoryBulkPriorGrid HistoryPrincipalIntegralAverage HistoryBulkReplacementGeometry
open HistoryBulkFibreSourceMean HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference HistoryBulkSpectatorReferenceRaw HistoryBulkReferenceScalarCoordinates
open HistoryBulkGiantIntegerReference HistoryBulkResidueNormSum ScaleBudget Filter

theorem reference_plain_prime_error_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k₀ : ℕ} (hBs : 0 ≤ Bs) (hk₀ : 0 < k₀) :
    ∀ᶠ L : ℝ in atTop, ∀ spectator : PrimeSource,
    (∀p : spectator.Sample, Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀ ds : Fin (2*(bulkSize k₀ L/2))→spectator.Sample,
    ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k₀ L E),
    Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
    C.blockBase-2 < (C.giantCenter:ℝ) →
    ∀ (l : ℕ) (_hl : l ≤ k₀)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k₀ L/2))))
    (x y : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l))
    (p q P Q : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
      (frequencyBound Bs BD Bz k₀ L) l)
    (_hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass x ≠ 0)
    (_hy : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass y ≠ 0)
    (_hc : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c ≠ 0)
    (_he : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e ≠ 0)
    (_hP : 0<P) (_hQ : 0<Q) (_hPc : |Real.log (P:ℝ)-(C.giantCenter:ℝ)|≤1)
    (_hQc : |Real.log (Q:ℝ)-(C.giantCenter:ℝ)|≤1),
    let outside := spectatorList spectator ds
    let seed := Template.initial (2*(bulkSize k₀ L/2)) k₀
    let V := frequencyBound Bs BD Bz k₀ L
    let T := Template.current seed l
    let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x p) P Q) c
    let g := decodeHistory C.sources seed V l (giantState (sourceState C.sources T y q) P Q) e
    ∀ (hs : h.Supported V outside) (gs : g.Supported V outside),
    ∀ (_hmatch : RootMatching h g)
      (eB : (Fin (2^l)×Fin (2*(bulkSize k₀ L/2))) ≃ bulkCoordinates h g),
    ∀ (hV : ∀r∈outside,∀j≤l,V j<r) (independent : Bool) (a : SelectedNonbulkSample C l),
    let N := bulkModulus h g outside k₀
    letI : NeZero N := ⟨actual_bulk_modulus_ne_zero h g hs gs (spectatorPrimes spectator ds) k₀⟩
    let F := rootTest independent false d h g hs gs (spectatorPrimes spectator ds) hV σ k₀
    let f := jointScalar C (bulkSize k₀ L/2) h g hs gs (boolEquiv h g) eB
    ∃ _hsize : (N:ℝ)<Real.exp (bulkLogLower L),
    ‖(selectedBulkPrior C l).cmean (fun u => F (sourceBulkUnits N C.sources (2*(bulkSize k₀ L/2)) k₀ l (fibreAssignment C a u)) * primeIntegral
      (fun _ : Bool=>C.giantCenter-1) (fun _=>C.giantCenter+1)
      (fun _=>Construction.logCellMass C.giantCenter ∅)
      (fun y=>primeJointCutoff C.giantCenter f y (orderedSourceValues C.sources (2*(bulkSize k₀ L/2)) k₀ l (fibreAssignment C a u)))) -
      HistorySelectedJointIntegralBounds.nestedPrimeIntegral L C.giantCenter E f*
        ResidueHaar.average F‖ ≤
      192*Real.exp (-Real.exp (bulk.target*L)) := by
  filter_upwards [HistoryBulkSelectedIntegralReplacement.reference_plain_prime_error_eventually d Bs BD Bz hBs hk₀]
    with L hAP
  intro spectator hspec ds E C hblock hcenter l hl σ x y p q P Q c e hx hy hc he hP hQ hPc hQc
  dsimp only
  intro hs gs hmatch eB hV independent a
  let h := decodeHistory C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
    (frequencyBound Bs BD Bz k₀ L) l
    (giantState (sourceState C.sources _ x p) P Q) c
  let g := decodeHistory C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
    (frequencyBound Bs BD Bz k₀ L) l
    (giantState (sourceState C.sources _ y q) P Q) e
  have : NeZero (bulkModulus h g (spectatorList spectator ds) k₀) :=
    ⟨actual_bulk_modulus_ne_zero h g hs gs (spectatorPrimes spectator ds) k₀⟩
  obtain ⟨hsize,herr⟩ := hAP spectator hspec ds E C hblock hcenter l hl σ x y p q P Q c e
    hx hy hc he hP hQ hPc hQc hs gs hmatch eB hV independent
  refine ⟨hsize,?_⟩
  let F := rootTest independent false d h g hs gs (spectatorPrimes spectator ds) hV σ k₀
  let f := jointScalar C (bulkSize k₀ L/2) h g hs gs (boolEquiv h g) eB
  have hmean := fibre_cmean_eq_sourceBulkMean C a
    (bulkModulus h g (spectatorList spectator ds) k₀) hsize F (fun z => primeIntegral
      (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1)
      (fun _ => Construction.logCellMass C.giantCenter ∅)
      (fun y => primeJointCutoff C.giantCenter f y z))
  exact (congrArg (fun z : ℂ => ‖z -
    HistorySelectedJointIntegralBounds.nestedPrimeIntegral L C.giantCenter E f *
      ResidueHaar.average F‖) hmean).le.trans herr

end Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacement

end

end OAI
