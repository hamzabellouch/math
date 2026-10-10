import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePhase
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryRegular
import OAI.NumberTheory.Ostmann.Characters.TemplateInputColumns
import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseReindex

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

abbrev PivotPrimeIndex (k j:ℕ) (hj:j<k) (width:Role→ℕ) :=
  Fin (width ((schedule k j).role (pivotSlot k j hj).val))
abbrev SurvivingPrimeIndex (k j:ℕ) (width:Role→ℕ) :=
  CopiedConstituent (schedule k j) j width⊕OutsideConstituent (schedule k j) j width

def actualPivotOutgoing (k j:ℕ) (hj:j<k) (width:Role→ℕ)
    (q:PivotPrimeIndex k j hj width→ℕ) [∀i,Fact (q i).Prime]
    (χ:∀i,MulChar (ZMod (q i)) ℂ) (a:∀i,ZMod (q i))
    (Y:ℕ) (u:ZMod (∏i,q i)) : ℂ :=
  outgoingPivotProduct q χ a
    (fun i => historyRegularKappa k width (χ i) (fun _ => initialKappa (χ i)) j
      (scheduledConstituentInput k j hj width (.inl i)))
    (fun _ => 1) Y u

def actualPivotSurviving (k j:ℕ) (hj:j<k) (width:Role→ℕ)
    (r:SurvivingPrimeIndex k j width→ℕ) [∀i,Fact (r i).Prime]
    (χ:∀i,MulChar (ZMod (r i)) ℂ) (a:∀i,ZMod (r i))
    (P:ℕ) (s:ℤ) (t:HistoryReconstruction.Tree j) : ℂ :=
  ∏i,survivingPrimeRow r i (χ i) (a i)
    (actualHistoryUnary k width (χ i) j s t (scheduledConstituentInput k j hj width (.inr i)))
    (fun h => constituentGraph k j width
      (scheduledConstituentInput k j hj width (.inr i))
      (scheduledConstituentInput k j hj width (.inr h)))
    (collapsedConstituentGraph (schedule k j) j width (pivotSlot k j hj)
      (graph k j) (intraGraph k j) (some i) none) P s

theorem norm_actualPivotOutgoing_le (k j:ℕ) (hj:j<k) (width:Role→ℕ)
    (q:PivotPrimeIndex k j hj width→ℕ) [∀i,Fact (q i).Prime]
    (χ:∀i,MulChar (ZMod (q i)) ℂ) (hχ:∀i,χ i≠1)
    (a:∀i,ZMod (q i)) (Y:ℕ) (u:ZMod (∏i,q i)) :
    ‖actualPivotOutgoing k j hj width q χ a Y u‖≤1 := by
  apply norm_outgoingPivotProduct_le
  intro i
  exact (norm_historyRegularKappa k width (χ i) _
    (fun _ => norm_initialKappa (χ i) (hχ i)) j _).le

theorem scheduled_pivot_regular (k j:ℕ) (hj:j<k) :
    (schedule k j).IsRegular j (pivotSlot k j hj).val :=
  ⟨(pivotSlot k j hj).property.1,Or.inr ⟨j,le_rfl,(pivotSlot k j hj).property.2⟩⟩

end Ostmann.Characters.Template

end

end OAI
