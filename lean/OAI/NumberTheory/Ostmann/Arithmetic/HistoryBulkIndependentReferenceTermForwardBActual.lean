import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTermForwardB
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionAncestors

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairPattern HistorySymbolicEncoding HistoryPairBulkTransport HistoryOccurrenceVariables
open HistoryBulkSupportConverse HistoryBulkSupportConversePlan HistoryBulkReferenceTests

theorem actual_orderedSourceIndicatorB_eq_one_of_supported
    {D : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice D Bs BD Bz k L E) {spectator : PrimeSource}
    (hsep : C.CrossRoleSeparation spectator) (V : ℕ→ℕ) (l : ℕ) (s t : ℤ)
    (gp gm gp' gm' : ℕ) (x₀ y₀ x y : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l))
    (π : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length))
    (hold : ∀i, (y₀ i).val=(x₀ (π i)).val)
    (hnew : ∀i, (y i).val=(x (π i)).val)
    (c d : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) V l) {outside : List ℕ}
    (hs : (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c).Supported V outside) (ks : (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ d).Supported V outside)
    (hs' : (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp' gm' x c).Supported V outside) (ks' : (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp' gm' y d).Supported V outside)
    (hfixed : ∀i : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length, ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x≠0)
    (hy : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass y≠0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l c≠0)
    (hd : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l d≠0)
    (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (V j))
 :
    orderedSourceIndicatorB C.sources (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ d) hs ks (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)) x gp' gm'=1 := by
  apply orderedSourceIndicatorB_eq_one_of_supported C.sources (2*(bulkSize k L/2)) k V l s t
    gp gm gp' gm' x₀ y₀ x y π hold hnew c d hs ks hs' ks' hfixed hx hy hc hd hfreq
  · exact HistoryBulkSourceCollision.newIntegerSample_ancestor_units C hsep V l x hx c hc
      s gp' gm' gp' gm'
  · exact HistoryBulkSourceCollision.newIntegerSample_ancestor_units C hsep V l y hy d hd
      t gp' gm' gp' gm'

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm

end

end OAI
