import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourceBasic
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

theorem orderedReference_primeMean_raw
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (V : ℕ→ℕ) (outside : List ℕ) (l K : ℕ)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (x₀ y₀ x y : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) (s t : ℤ)
    (gp gm : ℕ) (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) V l)
    (hs : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)).Supported V outside) (ks : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e)).Supported V outside)
    (b sw : ℕ) (X tb td G : ℝ)
    (π : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length))
    (hnew : ∀i, (y i).val=(x (π i)).val)
    (hprime : ∀q∈outside,q.Prime) :
    let seed := Template.initial (2*(bulkSize k L/2)) k
    let oldh := assignedHistory C.sources seed V l s gp gm x₀ c
    let oldk := assignedHistory C.sources seed V l t gp gm y₀ e
    let newh := assignedHistory C.sources seed V l s 1 1 x c
    let newk := assignedHistory C.sources seed V l t 1 1 y e
    let hh := root_matches (assignedLabels C.sources seed V l s gp gm x₀ c)
    let fixedB := integerInsertOrderedGiants (2*(bulkSize k L/2)) k oldh oldk hs hh
      (orderedIntegerSourceValues C.sources (2*(bulkSize k L/2)) k l x) (fun _=>0)
    let R := newReferenceResidueTest d K oldh oldk hs ks newh newk σ
      (sourceBulkUnits ((pairedFrequencyProduct oldh oldk)^(K+2)) C.sources
        (2*(bulkSize k L/2)) k l x) fixedB (rootResidueIndicator newh)
    let f := primeScalar b sw X tb td G (2*(bulkSize k L/2)) k oldh oldk hs ks hh
      (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l x)
    primeMean C.giant
      (orderedReferenceTerm C V outside l K σ x₀ y₀ x y s t gp gm c e hs ks
        b sw X tb td G (fun _ _=>1)) =
    staticPairMask newh newk outside * oldCompensation oldh oldk *
      guardedPeriodicSourcePrimeMean C.giantCenter ∅ C.giantPositive
        (newComparisonModulus newh oldh oldk outside K) R f := by
  dsimp only
  rw [← primeMean_masked_periodic]
  apply primeMean_congr_nonneg
  intro P Q hp hq
  rw [orderedReferenceTerm_eq_periodic_product C V outside l K σ x₀ y₀ x y s t gp gm
    c e hs ks b sw X tb td G (fun _ _=>1) P Q π hnew hp hq hprime]
  simp only [primeTerm,primeScalar,staticPairMask,oldCompensation,guardIndicator]
  split_ifs <;> ring

end Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSource

end

end OAI
