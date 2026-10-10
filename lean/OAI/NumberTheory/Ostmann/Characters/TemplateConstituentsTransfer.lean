import OAI.NumberTheory.Ostmann.Characters.TemplateConstituents

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

def intraStep (T : Layout) (j : ℕ) (intra : T.Slot → ℤ) : (T.step j).Slot → ℤ
  | .inl (i,t) => copySign t*intra i.val
  | .inr _ => 0

theorem constituent_transfer_same_copy (T : Layout) (j : ℕ) (width : Role → ℕ)
    (p : {i:T.Slot // T.IsPivot j i}) (b : T.Slot → T.Slot → ℤ) (intra : T.Slot → ℤ)
    (i h : CopiedConstituent T j width) (t : Bool) :
    liftGraph (T.step j) width (graphStep T j p b) (intraStep T j intra)
      ((nextConstituentEquiv T j width).symm (.inl (i,t)))
      ((nextConstituentEquiv T j width).symm (.inl (h,t))) =
    copySign t*liftGraph T width b intra (copiedConstituentOld T j width i)
      (copiedConstituentOld T j width h) := by
  classical
  rcases i with ⟨i,a⟩
  rcases h with ⟨h,c⟩
  by_cases hi:i=h
  · subst h
    by_cases ha:a=c
    · subst c
      simp +instances [Layout.step,liftGraph,nextConstituentEquiv,copiedConstituentOld]
    · simp +instances [Layout.step,liftGraph,nextConstituentEquiv,copiedConstituentOld,ha,intraStep]
  · have hv:i.val≠h.val := fun he => hi (Subtype.ext he)
    have hsum : (Sum.inl (i,t):(T.step j).Slot) ≠ Sum.inl (h,t) := by
      intro he
      exact hi (congrArg Prod.fst (Sum.inl.inj he))
    simp +instances [Layout.step,liftGraph,nextConstituentEquiv,copiedConstituentOld,
      hi,hv,hsum,graphStep,transferGraph,oldIndex]

theorem constituent_transfer_other_copy (T : Layout) (j : ℕ) (width : Role → ℕ)
    (p : {i:T.Slot // T.IsPivot j i}) (b : T.Slot → T.Slot → ℤ) (intra : T.Slot → ℤ)
    (i h : CopiedConstituent T j width) (t u : Bool) (htu:t≠u) :
    liftGraph (T.step j) width (graphStep T j p b) (intraStep T j intra)
      ((nextConstituentEquiv T j width).symm (.inl (i,t)))
      ((nextConstituentEquiv T j width).symm (.inl (h,u))) = copySign t*b i.1.val p.val := by
  classical
  rcases i with ⟨i,a⟩
  rcases h with ⟨h,c⟩
  have hsum : (Sum.inl (i,t):(T.step j).Slot) ≠ Sum.inl (h,u) := by
    intro he
    exact htu (congrArg Prod.snd (Sum.inl.inj he))
  simp +instances [Layout.step,liftGraph,nextConstituentEquiv,hsum,htu,graphStep,transferGraph,oldIndex]

theorem constituent_transfer_copied_outside (T : Layout) (j : ℕ) (width : Role → ℕ)
    (p : {i:T.Slot // T.IsPivot j i}) (b : T.Slot → T.Slot → ℤ) (intra : T.Slot → ℤ)
    (i : CopiedConstituent T j width) (h : OutsideConstituent T j width) (t : Bool) :
    liftGraph (T.step j) width (graphStep T j p b) (intraStep T j intra)
      ((nextConstituentEquiv T j width).symm (.inl (i,t)))
      ((nextConstituentEquiv T j width).symm (.inr h)) =
      copySign t*liftGraph T width b intra (copiedConstituentOld T j width i)
        (outsideConstituentOld T j width h) := by
  classical
  rcases i with ⟨i,a⟩
  rcases h with ⟨h,c⟩
  have hv:i.val≠h.val := fun he => h.property.2 (he ▸ i.property)
  simp +instances [Layout.step,liftGraph,nextConstituentEquiv,copiedConstituentOld,outsideConstituentOld,
    hv,graphStep,transferGraph,oldIndex]

theorem constituent_transfer_outside_copied (T : Layout) (j : ℕ) (width : Role → ℕ)
    (p : {i:T.Slot // T.IsPivot j i}) (b : T.Slot → T.Slot → ℤ) (intra : T.Slot → ℤ)
    (i : OutsideConstituent T j width) (h : CopiedConstituent T j width) (t : Bool) :
    liftGraph (T.step j) width (graphStep T j p b) (intraStep T j intra)
      ((nextConstituentEquiv T j width).symm (.inr i))
      ((nextConstituentEquiv T j width).symm (.inl (h,t))) =
      copySign t*liftGraph T width b intra (outsideConstituentOld T j width i)
        (copiedConstituentOld T j width h) := by
  classical
  rcases i with ⟨i,a⟩
  rcases h with ⟨h,c⟩
  have hv:i.val≠h.val := fun he => i.property.2 (he.symm ▸ h.property)
  simp +instances [Layout.step,liftGraph,nextConstituentEquiv,copiedConstituentOld,outsideConstituentOld,
    hv,graphStep,transferGraph,oldIndex]

theorem constituent_transfer_outside_outside (T : Layout) (j : ℕ) (width : Role → ℕ)
    (p : {i:T.Slot // T.IsPivot j i}) (b : T.Slot → T.Slot → ℤ) (intra : T.Slot → ℤ)
    (i h : OutsideConstituent T j width) :
    liftGraph (T.step j) width (graphStep T j p b) (intraStep T j intra)
      ((nextConstituentEquiv T j width).symm (.inr i))
      ((nextConstituentEquiv T j width).symm (.inr h))=0 := by
  classical
  rcases i with ⟨i,a⟩
  rcases h with ⟨h,c⟩
  simp +instances [Layout.step,liftGraph,nextConstituentEquiv,intraStep,graphStep,transferGraph]

end Ostmann.Characters.Template

end

end OAI
