import OAI.CategoryTheory.Globular.BoundaryCells

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] {D B : GlobularFrame K}

namespace Presentation
variable {e : Hom D B} {j : ℕ} {Y : K}
variable (f : GlobularSet.Hom (GlobularPresheaf.disk.{v} (j+1)).underlying (D.homGlob Y))
variable (a : GlobularSet.LiftStage (e.pre Y) f j)

noncomputable def boundaryDesc : B.bd (j+1) ⟶ Y :=
  ((B.boundaryEquiv (j+1)).equiv Y).symm (a.nextBoundary ⟨𝟙 _⟩)

@[reassoc] theorem boundaryDesc_left :
    B.left j ≫ boundaryDesc f a = a.app j le_rfl ⟨Globe.source j⟩ := by
  have h := ((B.boundaryEquiv (j+1)).equiv Y).apply_symm_apply (a.nextBoundary ⟨𝟙 _⟩)
  exact congrArg (fun b => b.1.1) h
@[reassoc] theorem boundaryDesc_right :
    B.right j ≫ boundaryDesc f a = a.app j le_rfl ⟨Globe.target j⟩ := by
  have h := ((B.boundaryEquiv (j+1)).equiv Y).apply_symm_apply (a.nextBoundary ⟨𝟙 _⟩)
  exact congrArg (fun b => b.1.2) h

@[reassoc] theorem boundaryApp_desc (k : ℕ) (hk : k ≤ j)
    (x : (GlobularPresheaf.disk.{v} (j+1)).underlying.Cell k) :
    B.boundaryApp j k hk x ≫ boundaryDesc f a = a.app k hk x := by
  change ULift.{v} (Globe.Face k (j+1)) at x
  rcases x with ⟨x⟩
  cases x with
  | id => exfalso; change j+1 ≤ j at hk; omega
  | face h ε =>
    rw [B.boundaryApp_face]
    by_cases hk' : k = j
    · subst k
      rw [B.boundaryCell_top]
      cases ε
      · exact boundaryDesc_left f a
      · exact boundaryDesc_right f a
    · have hk' : k < j := by omega
      erw [B.boundaryCell_low hk', Category.assoc, boundaryDesc_left]
      have h := a.evalFace_app (Globe.Face.face hk' ε) le_rfl hk ⟨Globe.source j⟩
      erw [B.homGlob_eval, GlobularPresheaf.underlying_evalFace] at h
      exact h.symm

theorem boundaryDesc_comm :
    e.bd (j+1) ≫ boundaryDesc f a = D.inc (j+1) ≫ f.app (j+1) ⟨𝟙 _⟩ := by
  apply (D.square j).hom_ext
  · rw [← Category.assoc, e.left, Category.assoc, boundaryDesc_left]
    exact (a.fac j le_rfl ⟨Globe.source j⟩).trans
      ((D.diskDiagram_cell f j ⟨Globe.source j⟩).trans (by
        change D.diagram.face (Nat.lt_succ_self j) false ≫ _ = _
        rw [CoGlobularObject.face_succ]
        exact Category.assoc _ _ _))
  · rw [← Category.assoc, e.right, Category.assoc, boundaryDesc_right]
    exact (a.fac j le_rfl ⟨Globe.target j⟩).trans
      ((D.diskDiagram_cell f j ⟨Globe.target j⟩).trans (by
        change D.diagram.face (Nat.lt_succ_self j) true ≫ _ = _
        rw [CoGlobularObject.face_succ]
        exact Category.assoc _ _ _))

variable [HasPushouts K]
noncomputable def oneSidedStage (e : Hom D B) (j : ℕ) :
    GlobularSet.LiftStage (e.pre (oneSided e (j+1)))
      (D.diskDiagram (j+1) (pushout.inr (e.bd (j+1)) (D.inc (j+1)))) j where
  app k hk x := B.boundaryApp j k hk x ≫ pushout.inl _ _
  source_app k hk x := by
    change B.boundaryApp j k _ _ ≫ _ = B.diagram.source k ≫ B.boundaryApp j (k+1) hk x ≫ _
    erw [B.boundaryApp_source]
    exact Category.assoc _ _ _
  target_app k hk x := by
    change B.boundaryApp j k _ _ ≫ _ = B.diagram.target k ≫ B.boundaryApp j (k+1) hk x ≫ _
    erw [B.boundaryApp_target]
    exact Category.assoc _ _ _
  fac k hk x := by
    change e.obj k ≫ B.boundaryApp j k hk x ≫ _ = D.diagram.eval x.down ≫ _
    erw [← Category.assoc, ← e.boundaryApp_naturality, Category.assoc,
      pushout.condition, ← Category.assoc, D.boundaryApp_inc]
    rfl

noncomputable def oneSidedPresentation (e : Hom D B) (j : ℕ) :
    Presentation e (GlobularPresheaf.disk.{v} (j+1)).underlying j where
  obj := oneSided e (j+1)
  base := D.diskDiagram (j+1) (pushout.inr _ _)
  stage := oneSidedStage e j
  desc f a := pushout.desc (boundaryDesc f a) (f.app (j+1) ⟨𝟙 _⟩) (boundaryDesc_comm f a)
  base_desc f a k x := by
    change (D.diagram.eval x.down ≫ pushout.inr _ _) ≫ _ = _
    erw [Category.assoc, pushout.inr_desc]
    exact (D.diskDiagram_cell f k x).symm
  stage_desc f a k hk x := by
    change (B.boundaryApp j k hk x ≫ pushout.inl _ _) ≫ _ = _
    erw [Category.assoc, pushout.inl_desc]
    exact boundaryApp_desc f a k hk x
  hom_ext := by
    intro Y f g hb hs
    apply pushout.hom_ext
    · apply (B.square j).hom_ext
      · have h := hs j le_rfl ⟨Globe.source j⟩
        change (B.boundaryCell j j le_rfl false ≫ _) ≫ f = (B.boundaryCell j j le_rfl false ≫ _) ≫ g at h
        rw [B.boundaryCell_top] at h
        exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))
      · have h := hs j le_rfl ⟨Globe.target j⟩
        change (B.boundaryCell j j le_rfl true ≫ _) ≫ f = (B.boundaryCell j j le_rfl true ≫ _) ≫ g at h
        rw [B.boundaryCell_top] at h
        exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))
    · have h := hb (j+1) ⟨𝟙 _⟩
      change (𝟙 _ ≫ pushout.inr _ _) ≫ f = (𝟙 _ ≫ pushout.inr _ _) ≫ g at h
      simpa only [Category.id_comp] using h
end Presentation
end GlobularFrame
end Grothendieck

end OAI
