import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTermConverse
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTermSupported

namespace OAI

open Erdos970

noncomputable section
open scoped Classical
namespace Ostmann.Arithmetic.HistoryBulkFixedReferenceTerm
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryPairSmoothXi HistoryGiantReferenceMean
open HistoryRepresentativeSourceSeparation

theorem sourceIntegrand_eq_referenceTerm
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (V : ℕ→ℕ) (outside : List ℕ) (l K : ℕ)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (x₀ x : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) (s t : ℤ)
    (gp gm : ℕ) (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) V l)
    (hs : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)).Supported V outside) (ks : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x₀) e)).Supported V outside)
    (b sw : ℕ) (X tb td G : ℝ)
    (Jmul : ℤ→ℤ→ℂ) (P Q : ℤ)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator) (hle : l≤K)
    (hfixed : ∀i : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length,((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x≠0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l c≠0) (he : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l e≠0)
    (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (V j))
    (hp : 0<P) (hq : 0<Q) (had : PairAdmissible (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x₀) e) outside)
    (hprime : ∀q∈outside,q.Prime) (houtfreq : ∀q∈outside,∀j≤l,V j<q) :
    sourceIntegrand d C.sources (Template.initial (2*(bulkSize k L/2)) k) V outside l
      (sourceState C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) x s) (sourceState C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x) t)
      c e Jmul b sw X tb td G P Q =
    referenceTerm C V outside l K σ x₀ x s t gp gm c e hs ks b sw X tb td G Jmul P Q := by
  by_cases hnew : (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c).Supported V outside ∧ (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x) e).Supported V outside
  · exact sourceIntegrand_eq_referenceTerm_of_supported C V outside l K σ x₀ x s t gp gm c e
      hs ks b sw X tb td G Jmul P Q hsep hle hfixed hx hc he hfreq hp.le hq.le had hnew.1 hnew.2
  · have href : referenceTerm C V outside l K σ x₀ x s t gp gm c e hs ks b sw X tb td G Jmul P Q=0 := by
      by_contra hz
      exact hnew (supported_of_referenceTerm_ne_zero C V outside l K σ x₀ x s t gp gm c e
        hs ks b sw X tb td G Jmul P Q hsep hle hfixed hx hc he hfreq hp hq hprime houtfreq hz)
    have hzero := HistorySignedResidues.supportedHistoryPairXi_eq_zero_of_not d V outside b sw X tb td G
      (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x) e) hnew
    change Jmul P Q * supportedHistoryPairXi d V outside b sw X tb td G (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x) e) = _
    rw [hzero,mul_zero,href]

end Ostmann.Arithmetic.HistoryBulkFixedReferenceTerm

end

end OAI
