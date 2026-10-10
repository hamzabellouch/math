import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTermOrderedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceMaskFactors
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceMaskSourceProducts

namespace OAI

open Erdos970

noncomputable section
open scoped Classical
namespace Ostmann.Arithmetic.HistoryBulkReferenceMask
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryPairSmoothXi HistoryBulkReferenceTests
open HistoryBulkReferenceScalarCoordinates HistorySignedSpectatorCRT HistoryGiantReferenceMean
open HistoryBulkResidueNormSum HistoryBulkSpectatorReferenceRaw HistoryFrequencyResidues
open HistorySignedResidueFactorization HistoryCRTIntegration HistorySignedSpectatorDiagram
open HistoryBulkIndependentReferenceTerm

theorem orderedReferenceTerm_eq_masked_product
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
      Jmul P Q * (((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c).compensationProduct:ℂ)*((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e).compensationProduct:ℂ)) * rootResidueIndicator (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c) (P,Q) *
      (residuePairSpectator (residueTransform d) outside outside.prod (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat y e) (P,Q)) * (independentRTest K (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) σ (P,Q)
        (sourceBulkUnits ((pairedFrequencyProduct (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e))^(K+2)) C.sources (2*(bulkSize k L/2)) k l x)) * (orderedSourceIndicatorB C.sources (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs ks
        (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)) x P Q) * (pairedRealXi b sw X tb td G (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs ks
        (insertOrderedGiants (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs
          (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c))
          (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l x)
          (fun a => if a then (Q:ℝ) else (P:ℝ)))) := by
  have hmod := assigned_rootModulus_eq C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s t P.toNat Q.toNat x y c e π hnew
  have hP : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c).root.giantPlus:ℤ)=P := by
    simpa only [assignedHistory,decodeHistory_root,assignedRoot] using Int.toNat_of_nonneg hp
  have hQ : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c).root.giantMinus:ℤ)=Q := by
    simpa only [assignedHistory,decodeHistory_root,assignedRoot] using Int.toNat_of_nonneg hq
  have he := pair_guarded_product_eq (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat y e) (residueTransform d) outside hprime
    (fun q _ => actual_residueTransform_zero d q) P Q hP hQ
    (by simp only [assignedHistory,decodeHistory_root,assignedRoot])
    (by simp only [assignedHistory,decodeHistory_root,assignedRoot]) hmod
    (Jmul P Q * (((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c).compensationProduct:ℂ)*((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e).compensationProduct:ℂ)) * (orderedSourceIndicatorB C.sources (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs ks
        (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)) x P Q) * (independentRTest K (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) σ (P,Q)
        (sourceBulkUnits ((pairedFrequencyProduct (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e))^(K+2)) C.sources (2*(bulkSize k L/2)) k l x)) * (pairedRealXi b sw X tb td G (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs ks
        (insertOrderedGiants (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs
          (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c))
          (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l x)
          (fun a => if a then (Q:ℝ) else (P:ℝ)))))
  unfold orderedReferenceTerm
  calc
    _ = (if (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c).root.Coprime outside ∧ (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat y e).root.Coprime outside then
      (Jmul P Q * (((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c).compensationProduct:ℂ)*((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e).compensationProduct:ℂ)) * (orderedSourceIndicatorB C.sources (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs ks
        (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)) x P Q) * (independentRTest K (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) σ (P,Q)
        (sourceBulkUnits ((pairedFrequencyProduct (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e))^(K+2)) C.sources (2*(bulkSize k L/2)) k l x)) * (pairedRealXi b sw X tb td G (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs ks
        (insertOrderedGiants (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs
          (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c))
          (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l x)
          (fun a => if a then (Q:ℝ) else (P:ℝ)))))*(residuePairSpectator (residueTransform d) outside outside.prod (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat y e) (P,Q)) else 0) := by
        simp only [assignedHistory,decodeHistory_root,assignedRoot]
        split_ifs <;> simp_all only [and_self, ite_true, ite_false]
        ring
    _ = _ := by rw [he]; ring

end Ostmann.Arithmetic.HistoryBulkReferenceMask

end

end OAI
