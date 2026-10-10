import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryRegular
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryTransfer

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem initialPhase_eq_actualHistoryUnary (k : ℕ) (width : Role → ℕ)
    (p : (schedule k 0).Constituent width → ℕ) [∀ i, Fact (p i).Prime]
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) (a : ∀ i, ZMod (p i)) (s : ℤ) :
    initialPhase p χ a s =
      (∏ i, ZMod.stdAddChar (-(a i*Construction.crtFrequency p s i))) *
        primeGraphPhase (constituentGraph k 0 width) p χ
          (fun i => actualHistoryUnary k width (χ i) 0 s PUnit.unit i) := by
  rw [initialPhase_separate]
  have hg : (fun i h : (schedule k 0).Constituent width => if i=h then (0:ℤ) else 1) =
      constituentGraph k 0 width := by
    funext i h
    by_cases he : i=h
    · subst h
      simp [constituentGraph,liftGraph]
    · rw [ite_eq_right he,constituentGraph_zero k width i h he]
  rw [hg]
  rfl

theorem complete_history_phase_product_transport (k j : ℕ) (hj : j<k) (width : Role → ℕ)
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
    ((∏ it, ((ν it:ℂ)*oldPrimeCopiedRow p it.1 it.2 (χ (.inl it)) b P)^copySign it.2)*
      (∏ i, ((ξ i true:ℂ)*oldPrimeSharedRow p i true (χ (.inr i)) b P)/
        ((ξ i false:ℂ)*oldPrimeSharedRow p i false (χ (.inr i)) b P))) =
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
  have hh := complete_phase_product_transport p hc χ a _ hself
    (historyCopiedUnaryUnits k j width p χ hχ s t ht)
    (historyOutsideUnaryUnits k j width p χ hχ s t ht) P s t.1.1 t.1.2 he hP hf
  have hu := funext (transferredUnary_eq_actualHistoryUnary k j hj width p χ hχ s t ht)
  rw [hu] at hh
  exact hh

theorem supportedHistoryUnary_regular (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ≠1) (S : List Bool → Finset ℤ)
    (hS : ∀ path f, f∈S path → (f:ZMod p)≠0) (j : ℕ) (hj : j≤k) (path : List Bool)
    (h : HistoryFrequencyLabels.SupportedHistory S j path)
    (i : (schedule k j).Constituent width) (hi : (schedule k j).IsRegular j i.1) :
    supportedHistoryUnary k width χ (fun _ => initialKappa χ) S j path h i =
      historyRegularKappa k width χ (fun _ => initialKappa χ) j i *
        χ (h.val.1:ZMod p)^(-(rowSign k j i.1:ℤ)) :=
  actualHistoryUnary_regular k width χ hχ j hj h.val.1 h.val.2
    (historyFrequencyUnits_of_range S hS h.property) i hi

end Ostmann.Characters.Template

end

end OAI
