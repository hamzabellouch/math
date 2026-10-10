import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceForwardR
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportAssigned

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm
open Construction Conclusion HistoryBulkSupportConverse HistoryBulkDiagramParameters
open HistoryPairBulkTransport HistoryBulkReferenceForwardR

theorem independentReferenceIndicator_eq_one_of_supported
    (K : ℕ) (sources : SourceFamily) (m k l : ℕ) (V : ℕ→ℕ) (outside : List ℕ)
    (x₀ y₀ x y : SourceAssignment sources (Template.current (Template.initial m k) l)) (s t : ℤ) (gp gm gp' gm' : ℕ)
    (c e : HistoryChoices sources (Template.initial m k) V l)
    (hfixed : ∀i : Fin ((Template.current (Template.initial m k) l)).length,(((Template.current (Template.initial m k) l)).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hnew : (assignedHistory sources (Template.initial m k) V l s gp' gm' x c).Supported V outside)
    (hnew' : (assignedHistory sources (Template.initial m k) V l t gp' gm'
      y e).Supported V outside)
    (hx : (assignmentPrior sources (Template.current (Template.initial m k) l)).mass x≠0)
    (hy : (assignmentPrior sources (Template.current (Template.initial m k) l)).mass y≠0)
    (hfixedy : ∀i : Fin ((Template.current (Template.initial m k) l)).length,(((Template.current (Template.initial m k) l)).get i).role≠.bulk → (y i).val=(y₀ i).val)
    (hc : choicesMass sources (Template.initial m k) V l c≠0)
    (he : choicesMass sources (Template.initial m k) V l e≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j))
    (hle : l≤K) :
    independentReferenceIndicator K
      (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c)
      (assignedHistory sources (Template.initial m k) V l t gp gm y₀ e)
      (assignedHistory sources (Template.initial m k) V l s gp' gm' x c)
      (assignedHistory sources (Template.initial m k) V l t gp' gm' y e) (gp',gm')=1 := by
  apply decoded_independent_reference_eq_one K sources (Template.initial m k) V l
    (assignedRoot sources (Template.current (Template.initial m k) l) s gp' gm' x) (assignedRoot sources (Template.current (Template.initial m k) l) t gp' gm' y)
    (assignedRoot sources (Template.current (Template.initial m k) l) s gp gm x₀) (assignedRoot sources (Template.current (Template.initial m k) l) t gp gm y₀)
    c e outside hnew hnew'
    (assignedRoot_matches sources (Template.current (Template.initial m k) l) s gp' gm' x)
    (assignedRoot_matches sources (Template.current (Template.initial m k) l) t gp' gm' y)
    (assignedSlots_source_mass_ne_zero sources (Template.current (Template.initial m k) l) x hx)
    (assignedSlots_source_mass_ne_zero sources (Template.current (Template.initial m k) l) y hy)
    hc he hfreq rfl rfl rfl rfl
  · exact assignedSlots_erase_eq sources (Template.current (Template.initial m k) l) x x₀ hfixed
  · exact assignedSlots_erase_eq sources (Template.current (Template.initial m k) l) y y₀ hfixedy
  · exact hle

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm

end

end OAI
