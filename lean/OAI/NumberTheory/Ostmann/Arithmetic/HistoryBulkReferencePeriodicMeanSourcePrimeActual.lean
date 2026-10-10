import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourcePrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourceScalar

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

theorem orderedReference_primeMean_jointScalar
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (outside : List ℕ) (l K : ℕ)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (x₀ y₀ x y : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) (s t : ℤ)
    (gp gm : ℕ) (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l)
    (hs : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l s gp gm x₀ c)).Supported (frequencyBound Bs BD Bz k L) outside) (ks : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l t gp gm y₀ e)).Supported (frequencyBound Bs BD Bz k L) outside)
    (sw : ℕ)
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
        (2*(bulkSize k L/2)) k l x) fixedB (rootResidueIndicator newh)
    let f := fun u => HistoryBulkGiantCorrectedBounds.jointScalar C sw oldh oldk hs ks
      (HistoryPairGiantCoordinates.boolEquiv oldh oldk)
      (HistoryPairBulkCoordinates.orderedEquiv (2*(bulkSize k L/2)) k oldh oldk hs hh) u
      (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l x)
    primeMean C.giant
      (orderedReferenceTerm C (frequencyBound Bs BD Bz k L) outside l K σ x₀ y₀ x y s t gp gm c e hs ks
        (bulkSize k L/2) sw C.scale C.bulkBin C.spectatorBin C.giantCenter (fun _ _=>1)) =
    staticPairMask newh newk outside * oldCompensation oldh oldk *
      guardedPeriodicSourcePrimeMean C.giantCenter ∅ C.giantPositive
        (newComparisonModulus newh oldh oldk outside K) R f := by
  have he := orderedReference_primeMean_raw C (frequencyBound Bs BD Bz k L) outside l K σ
    x₀ y₀ x y s t gp gm c e hs ks (bulkSize k L/2) sw C.scale C.bulkBin C.spectatorBin
    C.giantCenter π hnew hprime
  dsimp only at he ⊢
  simpa only [guardedPeriodicSourcePrimeMean,primeScalar_eq_jointScalar] using he

end Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSource

end

end OAI
