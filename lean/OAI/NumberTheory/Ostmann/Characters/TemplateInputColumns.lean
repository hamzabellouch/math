import OAI.NumberTheory.Ostmann.Characters.TemplateConstituentInput

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem constituentInput_pivot_column (T:Layout) (j:ℕ) (width:Role→ℕ)
    (p:{i:T.Slot // T.IsPivot j i}) (hp:∀q:{i:T.Slot // T.IsPivot j i},q=p)
    (b:T.Slot→T.Slot→ℤ) (intra:T.Slot→ℤ)
    (i:CopiedConstituent T j width⊕OutsideConstituent T j width)
    (a:Fin (width (T.role p.val))) :
    liftGraph T width b intra (constituentInputEquiv T j width p hp (.inr i))
      (constituentInputEquiv T j width p hp (.inl a)) =
        collapsedConstituentGraph T j width p b intra (some i) none := by
  rw [constituentInputEquiv_pivot]
  cases i with
  | inl i =>
    rw [constituentInputEquiv_copied]
    apply liftGraph_pivot_column
    intro he
    change i.1.val=p.val at he
    exact pivot_not_copied T j i.1.val (he.symm ▸ p.property) i.1.property
  | inr i =>
    rw [constituentInputEquiv_outside]
    apply liftGraph_pivot_column
    intro he
    change i.1.val=p.val at he
    exact i.1.property.1 (he.symm ▸ p.property)

theorem scheduledInput_pivot_column (k n:ℕ) (hn:n<k) (width:Role→ℕ)
    (i:CopiedConstituent (schedule k n) n width⊕OutsideConstituent (schedule k n) n width)
    (a:Fin (width ((schedule k n).role (pivotSlot k n hn).val))) :
    constituentGraph k n width (scheduledConstituentInput k n hn width (.inr i))
      (scheduledConstituentInput k n hn width (.inl a)) =
    collapsedConstituentGraph (schedule k n) n width (pivotSlot k n hn)
      (graph k n) (intraGraph k n) (some i) none :=
  constituentInput_pivot_column (schedule k n) n width (pivotSlot k n hn)
    (pivotSlot_unique k n hn) (graph k n) (intraGraph k n) i a

end Ostmann.Characters.Template

end

end OAI
