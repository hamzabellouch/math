import OAI.NumberTheory.Ostmann.Characters.TemplateConstituents

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

def constituentInputSigma (T:Layout) (j:ℕ) (width:Role→ℕ)
    (p:{i:T.Slot // T.IsPivot j i}) :
    Fin (width (T.role p.val)) ⊕ (CopiedConstituent T j width ⊕ OutsideConstituent T j width) ≃
      Σi:Option ({i:T.Slot // T.IsCopied j i} ⊕ {i:T.Slot // T.IsOutside j i}),
        Fin (width (T.role (oldIndex T j p i))) where
  toFun
    | .inl a => ⟨none,a⟩
    | .inr (.inl ⟨i,a⟩) => ⟨some (.inl i),a⟩
    | .inr (.inr ⟨i,a⟩) => ⟨some (.inr i),a⟩
  invFun
    | ⟨none,a⟩ => .inl a
    | ⟨some (.inl i),a⟩ => .inr (.inl ⟨i,a⟩)
    | ⟨some (.inr i),a⟩ => .inr (.inr ⟨i,a⟩)
  left_inv x := by rcases x with a | (⟨i,a⟩ | ⟨i,a⟩) <;> rfl
  right_inv x := by rcases x with ⟨_ | (i | i),a⟩ <;> rfl

def constituentInputEquiv (T:Layout) (j:ℕ) (width:Role→ℕ)
    (p:{i:T.Slot // T.IsPivot j i})
    (hp:∀q:{i:T.Slot // T.IsPivot j i},q=p) :
    Fin (width (T.role p.val)) ⊕ (CopiedConstituent T j width ⊕ OutsideConstituent T j width) ≃
      T.Constituent width :=
  (constituentInputSigma T j width p).trans (Equiv.sigmaCongrLeft (β:=fun i:T.Slot => Fin (width (T.role i))) (oldIndexEquiv T j p hp))

@[simp] theorem constituentInputEquiv_pivot (T:Layout) (j:ℕ) (width:Role→ℕ)
    (p:{i:T.Slot // T.IsPivot j i}) (hp:∀q:{i:T.Slot // T.IsPivot j i},q=p)
    (a:Fin (width (T.role p.val))) :
    constituentInputEquiv T j width p hp (.inl a)=⟨p.val,a⟩ := rfl

@[simp] theorem constituentInputEquiv_copied (T:Layout) (j:ℕ) (width:Role→ℕ)
    (p:{i:T.Slot // T.IsPivot j i}) (hp:∀q:{i:T.Slot // T.IsPivot j i},q=p)
    (i:CopiedConstituent T j width) :
    constituentInputEquiv T j width p hp (.inr (.inl i))=copiedConstituentOld T j width i := rfl

@[simp] theorem constituentInputEquiv_outside (T:Layout) (j:ℕ) (width:Role→ℕ)
    (p:{i:T.Slot // T.IsPivot j i}) (hp:∀q:{i:T.Slot // T.IsPivot j i},q=p)
    (i:OutsideConstituent T j width) :
    constituentInputEquiv T j width p hp (.inr (.inr i))=outsideConstituentOld T j width i := rfl

def scheduledConstituentInput (k n:ℕ) (hn:n<k) (width:Role→ℕ) :=
  constituentInputEquiv (schedule k n) n width (pivotSlot k n hn) (pivotSlot_unique k n hn)

end Ostmann.Characters.Template

end

end OAI
