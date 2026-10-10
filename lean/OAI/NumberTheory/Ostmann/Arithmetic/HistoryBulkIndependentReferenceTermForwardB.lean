import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransportIntegerCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceForwardBBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceForwardBRows
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsSourceLeft

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairPattern HistorySymbolicEncoding HistoryPairBulkTransport HistoryOccurrenceVariables
open HistoryBulkSupportConverse HistoryBulkSupportConversePlan HistoryBulkReferenceTests
open HistoryBulkReferenceForwardB

theorem orderedSourceIndicatorB_eq_one_of_supported
    (sources : SourceFamily) (m k : ℕ) (V : ℕ→ℕ) (l : ℕ) (s t : ℤ)
    (gp gm gp' gm' : ℕ) (x₀ y₀ x y : SourceAssignment sources (Template.current (Template.initial m k) l))
    (π : Equiv.Perm (Fin (Template.current (Template.initial m k) l).length))
    (hold : ∀i, (y₀ i).val=(x₀ (π i)).val)
    (hnew : ∀i, (y i).val=(x (π i)).val)
    (c d : HistoryChoices sources (Template.initial m k) V l) {outside : List ℕ}
    (hs : (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c).Supported V outside) (ks : (assignedHistory sources (Template.initial m k) V l t gp gm y₀ d).Supported V outside)
    (hs' : (assignedHistory sources (Template.initial m k) V l s gp' gm' x c).Supported V outside) (ks' : (assignedHistory sources (Template.initial m k) V l t gp' gm' y d).Supported V outside)
    (hfixed : ∀i : Fin (Template.current (Template.initial m k) l).length, ((Template.current (Template.initial m k) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hx : (assignmentPrior sources (Template.current (Template.initial m k) l)).mass x≠0)
    (hy : (assignmentPrior sources (Template.current (Template.initial m k) l)).mass y≠0)
    (hc : choicesMass sources (Template.initial m k) V l c≠0)
    (hd : choicesMass sources (Template.initial m k) V l d≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j))
    (hanc : ReferenceAncestorUnits sources (Template.initial m k) V l (assignedRoot sources (Template.current (Template.initial m k) l) s gp' gm' x) c (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp' gm' x) gp' gm')
    (hanc' : ReferenceAncestorUnits sources (Template.initial m k) V l (assignedRoot sources (Template.current (Template.initial m k) l) t gp' gm' y) d (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp' gm' y) gp' gm') :
    orderedSourceIndicatorB sources m k (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k) V l t gp gm y₀ d) hs ks (root_matches (assignedLabels sources (Template.initial m k) V l s gp gm x₀ c)) x gp' gm'=1 := by
  have hlines := reference_lines_squares_of_supported_source sources (Template.initial m k) V outside l
    (assignedRoot sources (Template.current (Template.initial m k) l) s gp gm x₀) (assignedRoot sources (Template.current (Template.initial m k) l) s gp' gm' x) c (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp gm x₀) (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp' gm' x) rfl hs hs'
    (assignedSlots_source_mass_ne_zero sources (Template.current (Template.initial m k) l) x hx) hc hfreq hanc
  have hlines' := reference_lines_squares_of_supported_source sources (Template.initial m k) V outside l
    (assignedRoot sources (Template.current (Template.initial m k) l) t gp gm y₀) (assignedRoot sources (Template.current (Template.initial m k) l) t gp' gm' y) d (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp gm y₀) (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp' gm' y) rfl ks ks'
    (assignedSlots_source_mass_ne_zero sources (Template.current (Template.initial m k) l) y hy) hd hfreq hanc'
  exact indicator_eq_one_of_reference_lines sources (Template.initial m k) V outside l
    (assignedRoot sources (Template.current (Template.initial m k) l) s gp gm x₀) (assignedRoot sources (Template.current (Template.initial m k) l) t gp gm y₀) (assignedRoot sources (Template.current (Template.initial m k) l) s gp' gm' x) (assignedRoot sources (Template.current (Template.initial m k) l) t gp' gm' y) c d (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp gm x₀) (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp gm y₀) (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp' gm' x) (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp' gm' y) hs ks _ gp' gm'
    (integerInsertOrderedGiants_left_projection sources m k V l s gp gm gp' gm'
      x₀ x c (assignedHistory sources (Template.initial m k) V l t gp gm y₀ d) hs hfixed gp' gm')
    (HistoryBulkIndependentReferenceTransport.integerInsertOrderedGiants_right_projection sources m k V l s t gp gm gp' gm'
      x₀ y₀ x y π hold hnew c d hs hfixed gp' gm') hlines hlines'

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm

end

end OAI
