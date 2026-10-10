import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnary
import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseConjugate

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem complete_history_phase_conjugate_transport (k j : ℕ) (hj : j<k) (width : Role → ℕ)
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
      crtPhase p a s * primeGraphPhase (transferGraph b) p χ
        (fun i => actualHistoryUnary k width (χ i) (j+1) s t
          ((nextConstituentEquiv (schedule k j) j width).symm i)) := by
  dsimp only
  have hself : ∀ i, (collapsedConstituentGraph (schedule k j) j width (pivotSlot k j hj)
      (graph k j) (intraGraph k j)) (some i) (some i)=0 := by
    intro i
    cases i <;> simp [collapsedConstituentGraph,liftGraph]
  have hf : ∀ (i : CopiedConstituent (schedule k j) j width) (b : Bool),
      (signedChildFrequency t.1.1 t.1.2 b:ZMod (p (.inl (i,b))))≠0 := by
    intro i b
    cases b
    · simpa [signedChildFrequency] using (ht (.inl (i,false))).2.2.root
    · exact (ht (.inl (i,true))).2.1.root
  have hν (ib : CopiedConstituent (schedule k j) j width × Bool) :
      ‖(historyCopiedUnaryUnits k j width p χ hχ s t ht ib:ℂ)‖=1 :=
    norm_actualHistoryUnary k width (χ (.inl ib)) (hχ _) j _ _ ((ht _).child ib.2) _
  have hξ (i : OutsideConstituent (schedule k j) j width) (b : Bool) :
      ‖(historyOutsideUnaryUnits k j width p χ hχ s t ht i b:ℂ)‖=1 :=
    norm_actualHistoryUnary k width (χ (.inr i)) (hχ _) j _ _ ((ht _).child b) _
  have hh := character_product_conjugate_transport p hc χ _ hself
    (historyCopiedUnaryUnits k j width p χ hχ s t ht) hν
    (historyOutsideUnaryUnits k j width p χ hχ s t ht) hξ P s t.1.1 t.1.2 he hP hf
  have hu := funext (transferredUnary_eq_actualHistoryUnary k j hj width p χ hχ s t ht)
  rw [hu] at hh
  rw [translation_product_transport p hc a P s t.1.1 t.1.2 he hP,hh]

end Ostmann.Characters.Template

end

end OAI
