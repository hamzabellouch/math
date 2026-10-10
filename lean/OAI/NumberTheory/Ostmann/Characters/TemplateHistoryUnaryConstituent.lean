import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePhase
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryModulus
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryReindex

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem actualHistoryPhase_next_reindex (k j : ℕ) (hj : j<k) (width : Role → ℕ)
    (p : UnaryOutputIndex k j width → ℕ) [∀ i, Fact (p i).Prime]
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) (a : ∀ i, ZMod (p i))
    (s : ℤ) (t : HistoryReconstruction.Tree (j+1)) :
    let e := nextConstituentEquiv (schedule k j) j width
    actualHistoryPhase k (j+1) width (fun i => p (e i)) (fun i => χ (e i))
      (fun i => a (e i)) s t =
      crtPhase p a s * primeGraphPhase
        (transferGraph (collapsedConstituentGraph (schedule k j) j width (pivotSlot k j hj)
          (graph k j) (intraGraph k j))) p χ
        (fun i => actualHistoryUnary k width (χ i) (j+1) s t (e.symm i)) := by
  dsimp only
  unfold actualHistoryPhase
  rw [crtPhase_product_reindex,next_history_graphPhase_reindex k j hj width]
  rfl

theorem complete_history_phase_constituent_transport (k j : ℕ) (hj : j<k) (width : Role → ℕ)
    (p : UnaryOutputIndex k j width → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i h => (p i).Coprime (p h)))
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) (hχ : ∀ i, χ i≠1)
    (a : ∀ i, ZMod (p i)) (P s : ℤ) (t : HistoryReconstruction.Tree (j+1))
    (ht : ∀ i, HistoryFrequencyUnits (p i) (j+1) s t)
    (he : s*P=t.1.1*(primeCopyProduct p false:ℤ)-t.1.2*(primeCopyProduct p true:ℤ))
    (hP : ∀ i, (P:ZMod (p i))≠0) :
    let b := collapsedConstituentGraph (schedule k j) j width (pivotSlot k j hj)
      (graph k j) (intraGraph k j)
    let ν := historyCopiedUnaryUnits k j width p χ hχ s t ht
    let ξ := historyOutsideUnaryUnits k j width p χ hχ s t ht
    ((∏ i, leftTranslation p a P t.1.1 i)*conj (∏ i, rightTranslation p a P t.1.2 i)*
      (∏ i, outsideTranslation p a P t.1.1 true i*conj (outsideTranslation p a P t.1.2 false i))) *
    (((∏ i, (ν (i,true):ℂ)*oldPrimeCopiedRow p i true (χ (.inl (i,true))) b P)*
      conj (∏ i, (ν (i,false):ℂ)*oldPrimeCopiedRow p i false (χ (.inl (i,false))) b P))*
      (∏ i, ((ξ i true:ℂ)*oldPrimeSharedRow p i true (χ (.inr i)) b P)*
        conj ((ξ i false:ℂ)*oldPrimeSharedRow p i false (χ (.inr i)) b P))) =
      actualHistoryPhase k (j+1) width
        (fun i => p (nextConstituentEquiv (schedule k j) j width i))
        (fun i => χ (nextConstituentEquiv (schedule k j) j width i))
        (fun i => a (nextConstituentEquiv (schedule k j) j width i)) s t := by
  dsimp only
  rw [actualHistoryPhase_next_reindex k j hj width p χ a s t]
  exact complete_history_phase_conjugate_transport k j hj width p hc χ hχ a P s t ht he hP

end Ostmann.Characters.Template

end

end OAI
