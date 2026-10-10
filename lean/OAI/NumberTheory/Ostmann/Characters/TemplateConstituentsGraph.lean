import OAI.NumberTheory.Ostmann.Characters.TemplateConstituentsTransfer

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem liftGraph_transfer (T : Layout) (j : ℕ) (width : Role → ℕ)
    (p : {i:T.Slot // T.IsPivot j i}) (b : T.Slot → T.Slot → ℤ) (intra : T.Slot → ℤ)
    (x y : (T.step j).Constituent width) :
    liftGraph (T.step j) width (graphStep T j p b) (intraStep T j intra) x y =
      transferGraph (collapsedConstituentGraph T j width p b intra)
        (nextConstituentEquiv T j width x) (nextConstituentEquiv T j width y) := by
  classical
  obtain ⟨x,rfl⟩ := (nextConstituentEquiv T j width).symm.surjective x
  obtain ⟨y,rfl⟩ := (nextConstituentEquiv T j width).symm.surjective y
  simp only [Equiv.apply_symm_apply]
  cases x with
  | inl x =>
    rcases x with ⟨i,t⟩
    cases y with
    | inl y =>
      rcases y with ⟨h,u⟩
      by_cases ht:t=u
      · subst u
        rw [constituent_transfer_same_copy]
        by_cases hi:i=h
        · subst h
          simp [transferGraph,liftGraph]
        · simp only [transferGraph,ite_true,ite_eq_right hi,collapsedConstituentGraph]
      · rw [constituent_transfer_other_copy T j width p b intra i h t u ht]
        simp only [transferGraph,ite_eq_right ht,collapsedConstituentGraph]
    | inr h =>
      rw [constituent_transfer_copied_outside]
      rfl
  | inr i =>
    cases y with
    | inl y =>
      rcases y with ⟨h,t⟩
      rw [constituent_transfer_outside_copied]
      rfl
    | inr h =>
      rw [constituent_transfer_outside_outside]
      rfl

theorem constituentGraph_succ (k n : ℕ) (hn:n<k) (width : Role → ℕ)
    (x y : (schedule k (n+1)).Constituent width) :
    constituentGraph k (n+1) width x y =
      transferGraph (collapsedConstituentGraph (schedule k n) n width (pivotSlot k n hn)
        (graph k n) (intraGraph k n))
        (nextConstituentEquiv (schedule k n) n width x)
        (nextConstituentEquiv (schedule k n) n width y) := by
  unfold constituentGraph
  rw [graph_succ k n hn]
  have hi : intraGraph k (n+1)=intraStep (schedule k n) n (intraGraph k n) := by
    funext i
    cases i <;> rfl
  rw [hi]
  exact liftGraph_transfer (schedule k n) n width (pivotSlot k n hn) (graph k n) (intraGraph k n) x y

end Ostmann.Characters.Template

end

end OAI
