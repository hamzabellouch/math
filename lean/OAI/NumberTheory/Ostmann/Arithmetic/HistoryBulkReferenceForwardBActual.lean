import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceForwardBSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionAncestors

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceForwardB
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairPattern HistorySymbolicEncoding HistoryPairBulkTransport HistoryOccurrenceVariables
open HistoryBulkSupportConverse HistoryBulkSupportConversePlan HistoryBulkReferenceTests

theorem actual_orderedSourceIndicatorB_eq_one_of_supported
    {D : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice D Bs BD Bz k L E) {spectator : PrimeSource}
    (hsep : C.CrossRoleSeparation spectator) (V : ℕ→ℕ) (l : ℕ) (s t : ℤ)
    (gp gm gp' gm' : ℕ) (x₀ x : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l))
    (π : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length))
    (hπ : ∀i, C.sources ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get (π i)).origin = C.sources ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get i).origin)
    (c d : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) V l) {outside : List ℕ}
    (hs : (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c).Supported V outside) (ks : (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm (sourceAssignmentPermutation C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) π hπ x₀) d).Supported V outside)
    (hs' : (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp' gm' x c).Supported V outside) (ks' : (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp' gm' (sourceAssignmentPermutation C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) π hπ x) d).Supported V outside)
    (hfixed : ∀i : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length, ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x≠0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l c≠0)
    (hd : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l d≠0)
    (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (V j))
 :
    orderedSourceIndicatorB C.sources (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm (sourceAssignmentPermutation C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) π hπ x₀) d) hs ks (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)) x gp' gm'=1 := by
  apply orderedSourceIndicatorB_eq_one_of_supported C.sources (2*(bulkSize k L/2)) k V l s t
    gp gm gp' gm' x₀ x π hπ c d hs ks hs' ks' hfixed hx hc hd hfreq
  · exact HistoryBulkSourceCollision.newIntegerSample_ancestor_units C hsep V l x hx c hc
      s gp' gm' gp' gm'
  · have hxp : (assignmentPrior C.sources _).mass
        (sourceAssignmentPermutation C.sources _ π hπ x)≠0 := by
      simpa only [sourceAssignmentPermutation_mass] using hx
    exact HistoryBulkSourceCollision.newIntegerSample_ancestor_units C hsep V l
      (sourceAssignmentPermutation C.sources _ π hπ x) hxp d hd t gp' gm' gp' gm'

end Ostmann.Arithmetic.HistoryBulkReferenceForwardB

end

end OAI
