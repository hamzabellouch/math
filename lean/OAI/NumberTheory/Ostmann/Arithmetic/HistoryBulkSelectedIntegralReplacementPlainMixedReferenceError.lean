import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacementPlainMixedReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedGiantDensityMass

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators ContDiff
namespace Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacement
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkIntegralReplacement
open HistoryBulkGiantCorrectedBounds HistoryGiantXiReplacementActual HistoryGiantReferenceSourceBounds
open HistoryGiantReferenceMean HistorySignedXiTransport HistorySelectedPairDerivativeBounds PrimeCellFreezing
open HistoryBulkPriorGrid HistoryPrincipalIntegralAverage HistoryBulkReplacementGeometry
open HistoryBulkGiantIntegerReference HistoryBulkResidueNormSum ScaleBudget Filter

theorem reference_plain_mixed_error_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
    ∀ (hV : ∀r∈outside,∀j≤l,V j<r) (independent : Bool),
    let N := bulkModulus h g outside k₀
    letI : NeZero N := ⟨actual_bulk_modulus_ne_zero h g hs gs (spectatorPrimes spectator ds) k₀⟩
    let F := rootTest independent true d h g hs gs (spectatorPrimes spectator ds) hV σ k₀
    let f := jointScalar C (bulkSize k₀ L/2) h g hs gs (optionEquiv h g) eB
    ∃ hsize : (N:ℝ)<Real.exp (bulkLogLower L),
    ‖sourceBulkMean L E C.bulkPositive N hsize F (fun x=>mixedIntegral
      (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
      (fun _ : Unit=>C.giantCenter-1) (fun _=>C.giantCenter+1)
      (fun _=>Construction.logCellMass C.giantCenter ∅)
      (fun y=>mixedJointCutoff C.giantCenter f y x)) -
      HistorySelectedJointIntegralBounds.nestedMixedIntegral L C.giantCenter E f*
        ResidueHaar.average F‖ ≤
      192*Real.exp (-Real.exp (bulk.target*L)) := by
  filter_upwards [reference_plain_mixed_eventually d Bs BD Bz hBs hk₀,
    HistorySelectedGiantDensityMass.selected_density_masses_eventually d Bs BD Bz k₀]
    with L hAP hMass
  intro spectator hspec ds E C hblock hcenter l hl σ x y p q P Q c e hx hy hc he hP hQ hPc hQc
  dsimp only
  intro hs gs hmatch eB hV independent
  have hden := hMass E C hblock hcenter
  obtain ⟨hsize,herr⟩ := hAP spectator hspec ds E C hden.1 l hl σ x y p q P Q c e
    hx hy hc he hP hQ hPc hQc hs gs hmatch eB hV independent
  refine ⟨hsize,?_⟩
  have hpay : (3*Real.exp (-Real.exp (bulk.target*L)))*
      MixedCellIntegralFreezing.mixedLogMass 1 (C.giantCenter-1) (C.giantCenter+1)
      C.giantCenter smoothPartition (fun _ : Unit=>(Construction.logCellMass C.giantCenter ∅)⁻¹)
      (fun _=>C.giantCenter-1) (fun _=>C.giantCenter+1) ≤ 192*Real.exp (-Real.exp (bulk.target*L)) := by
    calc
      _ ≤ (3*Real.exp (-Real.exp (bulk.target*L)))*64 :=
        mul_le_mul_of_nonneg_left hden.2.2.2 (by positivity)
      _ = _ := by ring
  exact herr.trans hpay

end Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacement

end

end OAI
