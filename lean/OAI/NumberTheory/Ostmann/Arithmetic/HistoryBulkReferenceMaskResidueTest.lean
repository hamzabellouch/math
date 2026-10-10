import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportValues
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceMaskActual

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceMask
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryPairSmoothXi HistoryBulkReferenceTests
open HistoryBulkReferenceScalarCoordinates HistorySignedSpectatorCRT HistoryGiantReferenceMean
open HistoryBulkResidueNormSum HistoryBulkSpectatorReferenceRaw HistoryFrequencyResidues
open HistorySignedResidueFactorization HistoryCRTIntegration HistoryBulkIndependentReferenceTerm
open HistoryBulkGiantPrincipalTransport

theorem orderedReferenceTerm_eq_newResidueTest
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (V : ℕ→ℕ) (outside : List ℕ) (l K : ℕ)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (x₀ y₀ x y : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) (s t : ℤ)
    (gp gm : ℕ) (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) V l)
    (hs : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)).Supported V outside) (ks : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e)).Supported V outside)
    (b sw : ℕ) (X tb td G : ℝ)
    (Jmul : ℤ→ℤ→ℂ) (P Q : ℤ)
    (π : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length))
    (hnew : ∀i, (y i).val=(x (π i)).val)
    (hp : 0≤P) (hq : 0≤Q) (hprime : ∀q∈outside,q.Prime) :
    orderedReferenceTerm C V outside l K σ x₀ y₀ x y s t gp gm c e hs ks b sw X tb td G Jmul P Q =
    guardIndicator (((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
      ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat y e).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime) * guardIndicator (Nat.Coprime P.natAbs Q.natAbs) *
      Jmul P Q * (((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c).compensationProduct:ℂ)*((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e).compensationProduct:ℂ)) *
      newReferenceResidueTest d K (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs ks (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat y e) σ (sourceBulkUnits ((pairedFrequencyProduct (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e))^(K+2)) C.sources (2*(bulkSize k L/2)) k l x) (integerInsertOrderedGiants (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)) (orderedIntegerSourceValues C.sources (2*(bulkSize k L/2)) k l x) (fun _=>0))
        (rootResidueIndicator (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c)) (P,Q) * (pairedRealXi b sw X tb td G (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs ks
      (insertOrderedGiants (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c))
        (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l x) (fun a => if a then (Q:ℝ) else (P:ℝ)))) := by
  rw [orderedReferenceTerm_eq_masked_product C V outside l K σ x₀ y₀ x y s t gp gm c e
    hs ks b sw X tb td G Jmul P Q π hnew hp hq hprime]
  simp only [newReferenceResidueTest, referenceResidueTest, projectedRingPair, map_intCast]
  rw [←orderedSourceIndicatorB_eq_fixed_giants C.sources (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs ks (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)) x P Q]
  ring

end Ostmann.Arithmetic.HistoryBulkReferenceMask

end

end OAI
