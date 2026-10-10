import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourcePrime

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

theorem orderedReference_means_eq_zero_of_static
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
    (hprime : ∀q∈outside,q.Prime)
    (J : ℤ→ℤ→ℂ)
    (hzero : staticPairMask
      (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s 1 1 x c)
      (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t 1 1 y e)
      outside=0) :
    primeMean C.giant
      (orderedReferenceTerm C V outside l K σ x₀ y₀ x y s t gp gm c e hs ks
        b sw X tb td G J)=0 ∧
    mixedMean C.giantCenter C.giant
      (orderedReferenceTerm C V outside l K σ x₀ y₀ x y s t gp gm c e hs ks
        b sw X tb td G J)=0 := by
  have hz (P Q : ℤ) (hp : 0≤P) (hq : 0≤Q) :
      orderedReferenceTerm C V outside l K σ x₀ y₀ x y s t gp gm c e hs ks
        b sw X tb td G J P Q=0 := by
    rw [orderedReferenceTerm_eq_periodic_product C V outside l K σ x₀ y₀ x y s t gp gm
      c e hs ks b sw X tb td G J P Q π hnew hp hq hprime]
    simp only [staticPairMask] at hzero
    rw [hzero]
    simp only [zero_mul]
  constructor
  · rw [primeMean_congr_nonneg C.giant _ (fun _ _=>0) hz]
    simp only [primeMean,FinitePrior.cmean,mul_zero,Finset.sum_const_zero]
  · rw [mixedMean_congr_nonneg C.giantCenter C.giant _ (fun _ _=>0) hz]
    simp only [mixedMean,FinitePrior.cmean,mul_zero,Finset.sum_const_zero]

end Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSource

end

end OAI
