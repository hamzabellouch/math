import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceForwardBBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceForwardBRows
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsSourceRight

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceForwardB
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairPattern HistorySymbolicEncoding HistoryPairBulkTransport HistoryOccurrenceVariables
open HistoryBulkSupportConverse HistoryBulkSupportConversePlan HistoryBulkReferenceTests

theorem orderedSourceIndicatorB_eq_one_of_supported
    (sources : SourceFamily) (m k : ℕ) (V : ℕ→ℕ) (l : ℕ) (s t : ℤ)
    (gp gm gp' gm' : ℕ) (x₀ x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (π : Equiv.Perm (Fin (Template.current (Template.initial m k) l).length))
    (hπ : ∀i, sources ((Template.current (Template.initial m k) l).get (π i)).origin = sources ((Template.current (Template.initial m k) l).get i).origin)
    (c d : HistoryChoices sources (Template.initial m k) V l) {outside : List ℕ}
    (hs : (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c).Supported V outside) (ks : (assignedHistory sources (Template.initial m k) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀) d).Supported V outside)
    (hs' : (assignedHistory sources (Template.initial m k) V l s gp' gm' x c).Supported V outside) (ks' : (assignedHistory sources (Template.initial m k) V l t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x) d).Supported V outside)
    (hfixed : ∀i : Fin (Template.current (Template.initial m k) l).length, ((Template.current (Template.initial m k) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hx : (assignmentPrior sources (Template.current (Template.initial m k) l)).mass x≠0)
    (hc : choicesMass sources (Template.initial m k) V l c≠0)
    (hd : choicesMass sources (Template.initial m k) V l d≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j))
    (hanc : ReferenceAncestorUnits sources (Template.initial m k) V l (assignedRoot sources (Template.current (Template.initial m k) l) s gp' gm' x) c (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp' gm' x) gp' gm')
    (hanc' : ReferenceAncestorUnits sources (Template.initial m k) V l (assignedRoot sources (Template.current (Template.initial m k) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x)) d (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x)) gp' gm') :
    orderedSourceIndicatorB sources m k (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀) d) hs ks (root_matches (assignedLabels sources (Template.initial m k) V l s gp gm x₀ c)) x gp' gm'=1 := by
  have hxp : (assignmentPrior sources (Template.current (Template.initial m k) l)).mass (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x)≠0 := by
    simpa only [sourceAssignmentPermutation_mass] using hx
  have hlines := reference_lines_squares_of_supported_source sources (Template.initial m k) V outside l
    (assignedRoot sources (Template.current (Template.initial m k) l) s gp gm x₀) (assignedRoot sources (Template.current (Template.initial m k) l) s gp' gm' x) c (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp gm x₀) (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp' gm' x) rfl hs hs'
    (assignedSlots_source_mass_ne_zero sources (Template.current (Template.initial m k) l) x hx) hc hfreq hanc
  have hlines' := reference_lines_squares_of_supported_source sources (Template.initial m k) V outside l
    (assignedRoot sources (Template.current (Template.initial m k) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀)) (assignedRoot sources (Template.current (Template.initial m k) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x)) d (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀)) (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x)) rfl ks ks'
    (assignedSlots_source_mass_ne_zero sources (Template.current (Template.initial m k) l) (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x) hxp) hd hfreq hanc'
  exact indicator_eq_one_of_reference_lines sources (Template.initial m k) V outside l
    (assignedRoot sources (Template.current (Template.initial m k) l) s gp gm x₀) (assignedRoot sources (Template.current (Template.initial m k) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀)) (assignedRoot sources (Template.current (Template.initial m k) l) s gp' gm' x) (assignedRoot sources (Template.current (Template.initial m k) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x)) c d (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp gm x₀) (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀)) (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp' gm' x) (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x)) hs ks _ gp' gm'
    (integerInsertOrderedGiants_left_projection sources m k V l s gp gm gp' gm'
      x₀ x c (assignedHistory sources (Template.initial m k) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k) l) π hπ x₀) d) hs hfixed gp' gm')
    (integerInsertOrderedGiants_right_projection sources m k V l s t gp gm gp' gm'
      x₀ x π hπ c d hs hfixed gp' gm') hlines hlines'

end Ostmann.Arithmetic.HistoryBulkReferenceForwardB

end

end OAI
