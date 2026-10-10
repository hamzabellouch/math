import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTerm
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeIntegerAdmissible

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFixedReferenceTerm
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryGiantReferenceMean HistorySignedXiTransport

theorem sourceIntegrand_eq_referenceTerm_of_source_masses
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
    (hx₀ : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x₀≠0)
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x≠0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l c≠0) (he : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l e≠0)
    (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (V j))
    (hp : 0<P) (hq : 0<Q)
    (hprime : ∀q∈outside,q.Prime) (houtfreq : ∀q∈outside,∀j≤l,V j<q) :
    sourceIntegrand d C.sources (Template.initial (2*(bulkSize k L/2)) k) V outside l
      (sourceState C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) x s) (sourceState C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x) t)
      c e Jmul b sw X tb td G P Q =
    referenceTerm C V outside l K σ x₀ x s t gp gm c e hs ks b sw X tb td G Jmul P Q := by
  have hx₀' : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x₀)≠0 := by
    change (assignmentPrior C.sources _).mass (sourceAssignmentPermutation C.sources _ _ _ x₀)≠0
    erw [sourceAssignmentPermutation_mass]
    exact hx₀
  have had := HistoryRepresentativeIntegerAdmissible.decoded_integer_pair_admissible C hsep V outside l
    x₀ ((leafBulkAssignmentPermutation (bulkSize k L/2) k l C.bulk (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ) x₀) s t gp gm c e hx₀ hx₀' hc he hfreq
    (fun q hq => ⟨hprime q hq,houtfreq q hq⟩)
    (by simpa only [giantState,sourceState,Int.toNat_natCast,assignedHistory,assignedRoot] using hs)
    (by simpa only [giantState,sourceState,Int.toNat_natCast,assignedHistory,assignedRoot] using ks)
  apply sourceIntegrand_eq_referenceTerm C V outside l K σ x₀ x s t gp gm c e hs ks
    b sw X tb td G Jmul P Q hsep hle hfixed hx hc he hfreq hp hq ?_ hprime houtfreq
  simpa only [giantState,sourceState,Int.toNat_natCast,assignedHistory,assignedRoot] using had

end Ostmann.Arithmetic.HistoryBulkFixedReferenceTerm

end

end OAI
