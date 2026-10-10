import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequencyBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceForwardRSource

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequency
open Construction Conclusion HistoryBulkProducts HistoryFrequencyResidues
open HistoryBulkSupportConverse HistoryBulkResidueNormSum HistoryPairBulkTransport HistoryBulkDiagramParameters
open HistoryPairedFrequencyAverageHaar HistoryBulkSpectatorReferenceRaw CanonicalHistoryLeafBulk

theorem independentRTest_eq_one_of_supported
    (K m k l : ℕ) (sources : SourceFamily) (V : ℕ→ℕ) (outside : List ℕ)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (x₀ y₀ x y : SourceAssignment sources (Template.current (Template.initial m k) l))
    (s t : ℤ) (gp gm gp' gm' : ℕ)
    (c e : HistoryChoices sources (Template.initial m k) V l)
    (hfixed : ∀i : Fin (Template.current (Template.initial m k) l).length,
      ((Template.current (Template.initial m k) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hfixed' : ∀i : Fin (Template.current (Template.initial m k) l).length,
      ((Template.current (Template.initial m k) l).get i).role≠.bulk → (y i).val=(y₀ i).val)
    (hbulk : ∀u : Fin (2^l)×Fin m,
      bulkSamples sources m k l y u.1 u.2=bulkSamples sources m k l x (σ u).1 (σ u).2)
    (hs : (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c).Supported V outside)
    (hs' : (assignedHistory sources (Template.initial m k) V l t gp gm y₀ e).Supported V outside)
    (hnew : (assignedHistory sources (Template.initial m k) V l s gp' gm' x c).Supported V outside)
    (hnew' : (assignedHistory sources (Template.initial m k) V l t gp' gm' y e).Supported V outside)
    (hx : (assignmentPrior sources (Template.current (Template.initial m k) l)).mass x≠0)
    (hy : (assignmentPrior sources (Template.current (Template.initial m k) l)).mass y≠0)
    (hc : choicesMass sources (Template.initial m k) V l c≠0)
    (he : choicesMass sources (Template.initial m k) V l e≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j)) (hle : l≤K) :
    independentRTest K
      (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c)
      (assignedHistory sources (Template.initial m k) V l t gp gm y₀ e)
      σ (gp',gm')
      (sourceBulkUnits
        ((pairedFrequencyProduct (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c)
          (assignedHistory sources (Template.initial m k) V l t gp gm y₀ e))^(K+2)) sources m k l x)=1 := by
  rw [independentRTest_source_eq_reference_of_mass K m k l sources V
    (assignedHistory sources (Template.initial m k) V l s gp gm x₀ c)
    (assignedHistory sources (Template.initial m k) V l t gp gm y₀ e)
    (assignedRoot sources _ s gp' gm' x) (assignedRoot sources _ t gp' gm' y)
    c e x y σ rfl rfl hbulk hs hs' hx hfreq]
  apply HistoryBulkReferenceForwardR.decoded_independent_reference_eq_one K sources (Template.initial m k) V l
    (assignedRoot sources _ s gp' gm' x) (assignedRoot sources _ t gp' gm' y)
    (assignedRoot sources _ s gp gm x₀) (assignedRoot sources _ t gp gm y₀)
    c e outside hnew hnew'
    (assignedRoot_matches sources _ s gp' gm' x) (assignedRoot_matches sources _ t gp' gm' y)
    (assignedSlots_source_mass_ne_zero sources _ x hx) (assignedSlots_source_mass_ne_zero sources _ y hy)
    hc he hfreq rfl rfl rfl rfl
  · exact assignedSlots_erase_eq sources _ x x₀ hfixed
  · exact assignedSlots_erase_eq sources _ y y₀ hfixed'
  · exact hle

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequency

end

end OAI
