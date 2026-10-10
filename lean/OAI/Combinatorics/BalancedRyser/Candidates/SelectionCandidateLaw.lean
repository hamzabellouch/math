import OAI.Combinatorics.BalancedRyser.Candidates.CandidateSelectionBridge
import OAI.Combinatorics.BalancedRyser.Selection.SelectionPushforward2

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [eqF : DecidableEq F]

theorem candidateSelection_label_injective (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F)) (s : Slot F) :
    Set.InjOn (fun v : AvailableCandidate M => v.val.2)
      {v | (candidateSelectionInput M J).slot v = s} := by
  intro v hv w hw heq
  apply Subtype.ext
  exact Prod.ext (hv.trans hw.symm) heq

theorem candidateSelection_label_supported (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (law : Selection.OutputLaw (candidateSelectionInput M J))
    (f : Slot F → F)
    (hf : 0 < law.labelWeight (fun _ v => v.val.2) f) :
    CandidateSelector M f ∧ IndependentSelector M f := by
  obtain ⟨a, ha, hpos⟩ := FinitePushforward.exists_positive_preimage
    (FinitePushforward.mapChoices (fun (_ : Slot F) (v : AvailableCandidate M) => v.val.2))
    law.weight law.nonnegative f hf
  have hs := candidateSelection_selector_of_transversal M J a (law.supported a hpos)
  exact ha ▸ hs

theorem candidateSelection_label_configuration (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (law : Selection.OutputLaw (candidateSelectionInput M J))
    (hd : DistinctConstituents M) (f : Slot F → F)
    (hf : 0 < law.labelWeight (fun _ v => v.val.2) f) :
    (selectedConfiguration M f).Valid ∧ (selectedConfiguration M f).Compatible := by
  obtain ⟨hs, hi⟩ := candidateSelection_label_supported M J law f hf
  exact ⟨selectedConfiguration_valid hd hs,
    (selectedConfiguration_compatible_iff hs).mpr hi⟩

theorem candidateSelection_nonempty (M : MergedPairs F) {c C : ℝ}
    (hc : 0 < c) (hgood : CandidateGraphGood M c C) :
    Nonempty (AvailableCandidate M) := by
  have hq : 0 < (Fintype.card F : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hslot : 0 < (candidateSlot M (none, false)).card := by
    exact_mod_cast (mul_pos hc hq).trans_le ((hgood.1 (none, false)).1)
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hslot
  exact ⟨⟨v, (Finset.mem_filter.mp hv).1⟩⟩

local instance : DecidableEq (Slot F) := Classical.decEq _

theorem candidateSelection_label_event (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (law : Selection.OutputLaw (candidateSelectionInput M J))
    (P : (Slot F → F) → Prop) :
    (∑ f, if P f then law.labelWeight (fun _ v => v.val.2) f else 0) =
      ∑ a, if P (fun i => (a i).val.2) then law.weight a else 0 := by
  exact FinitePushforward.eventMass_pushWeight
    (FinitePushforward.mapChoices (fun (_ : Slot F) (v : AvailableCandidate M) => v.val.2))
    law.weight P

theorem candidateSelection_label_cylinder (M : MergedPairs F) {c C K : ℝ}
    (hc : 0 < c) (hgood : CandidateGraphGood M c C)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (law : Selection.OutputLaw (candidateSelectionInput M J))
    (hbound : ∀ (S : Finset (Slot F)) (a : Slot F → AvailableCandidate M),
      Selection.cylinderMass law S a ≤ (K / (Fintype.card F : ℝ)) ^ S.card)
    (S : Finset (Slot F)) (f : Slot F → F) :
    FinitePushforward.cylinderMass (law.labelWeight (fun _ v => v.val.2)) S f ≤
      (K / (Fintype.card F : ℝ)) ^ S.card := by
  cases Subsingleton.elim eqF (Classical.decEq F)
  let := candidateSelection_nonempty M hc hgood
  exact Selection.labelWeight_cylinder_le law (fun _ v => v.val.2)
    (candidateSelection_label_injective M J) _ hbound S f

end
end Balanced

end OAI
