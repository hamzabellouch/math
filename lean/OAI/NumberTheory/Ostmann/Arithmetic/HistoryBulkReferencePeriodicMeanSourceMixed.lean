import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourceMixedFactor
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourcePrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourceScalarMixed

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSource
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryPairSmoothXi HistoryBulkReferenceTests
open HistoryBulkReferenceScalarCoordinates HistorySignedSpectatorCRT HistoryGiantReferenceMean
open HistoryBulkResidueNormSum HistoryBulkSpectatorReferenceRaw HistoryFrequencyResidues
open HistorySignedResidueFactorization HistoryCRTIntegration HistoryBulkIndependentReferenceTerm
open HistoryBulkGiantPrincipalTransport HistoryBulkReferenceNewModuli HistoryBulkReferenceMask
open HistoryBulkReferencePeriodicMean HistoryGiantWeightedPriorReplacement
open HistoryBulkReferenceSmallMultiplier HistoryDiagonalSmallOriginalMean
open HistorySignedResidueWeightedAverages DiagonalSmallResidueNorm

theorem orderedReference_mixedMean_raw
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (outside : List ℕ) (l K : ℕ)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (x₀ y₀ x y : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) (s t : ℤ)
    (gp gm : ℕ) (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l)
    (hs : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l s gp gm x₀ c)).Supported (frequencyBound Bs BD Bz k L) outside) (ks : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l t gp gm y₀ e)).Supported (frequencyBound Bs BD Bz k L) outside)
    (sw : ℕ)
    (hu : SmallUnitData outside.prod 1 1 (currentOuterSlots C x) (currentRemainingSlots C x) s)
    (π : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length))
    (hnew : ∀i, (y i).val=(x (π i)).val)
    (hprime : ∀q∈outside,q.Prime) :
    let seed := Template.initial (2*(bulkSize k L/2)) k
    let oldh := assignedHistory C.sources seed (frequencyBound Bs BD Bz k L) l s gp gm x₀ c
    let oldk := assignedHistory C.sources seed (frequencyBound Bs BD Bz k L) l t gp gm y₀ e
    let newh := assignedHistory C.sources seed (frequencyBound Bs BD Bz k L) l s 1 1 x c
    let newk := assignedHistory C.sources seed (frequencyBound Bs BD Bz k L) l t 1 1 y e
    let hh := root_matches (assignedLabels C.sources seed (frequencyBound Bs BD Bz k L) l s gp gm x₀ c)
    let fixedB := integerInsertOrderedGiants (2*(bulkSize k L/2)) k oldh oldk hs hh
      (orderedIntegerSourceValues C.sources (2*(bulkSize k L/2)) k l x) (fun _=>0)
    let R := newReferenceResidueTest d K oldh oldk hs ks newh newk σ
      (sourceBulkUnits ((pairedFrequencyProduct oldh oldk)^(K+2)) C.sources
        (2*(bulkSize k L/2)) k l x) fixedB (fun z=>rootResidueIndicator newh z *
        mixedExtension (currentRootSmallTest C outside x s c hu) z)
    let f := mixedScalar (bulkSize k L/2) sw C.scale C.bulkBin C.spectatorBin C.giantCenter
      (2*(bulkSize k L/2)) k oldh oldk hs ks hh
      (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l x)
    mixedMean C.giantCenter C.giant
      (orderedReferenceTerm C (frequencyBound Bs BD Bz k L) outside l K σ x₀ y₀ x y s t gp gm c e hs ks
        (bulkSize k L/2) sw C.scale C.bulkBin C.spectatorBin C.giantCenter (fun P Q=>(smallMultiplier C outside x s P Q:ℂ))) =
    staticPairMask newh newk outside * oldCompensation oldh oldk *
      guardedPeriodicSourceMixedMean C.giantCenter ∅ C.giantPositive
        (newComparisonModulus newh oldh oldk outside K) R f := by
  dsimp only
  rw [←mixedMean_masked_periodic]
  apply mixedMean_congr_nonneg
  intro P Q hp hq
  rw [orderedReferenceTerm_eq_periodic_product C (frequencyBound Bs BD Bz k L)
    outside l K σ x₀ y₀ x y s t gp gm c e hs ks (bulkSize k L/2) sw C.scale
    C.bulkBin C.spectatorBin C.giantCenter (fun P Q=>(smallMultiplier C outside x s P Q:ℂ))
    P Q π hnew hp hq hprime]
  simp only [mixedTerm,mixedScalar,primeScalar,staticPairMask,oldCompensation,guardIndicator,Option.elim']
  erw [←smallMultiplier_mul_newReferenceResidueTest C outside K _ _ hs ks
    x s c _ σ _ _ hu P Q hp hq]
  split_ifs <;> ring

end Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSource

end

end OAI
