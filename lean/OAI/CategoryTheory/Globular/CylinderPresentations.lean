import OAI.CategoryTheory.Globular.SkeletalPresentation

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularSet

def whiskerDescOriented {X Y : GlobularSet.{u}} (n : ℕ) (ε : Bool) (f : Hom X Y)
    (e : X.Cell n → Y.Cell (n+1))
    (he : ∀ x, (if ε then Y.target n else Y.source n) (e x) = f.app n x) :
    Hom (X.whisker n ε) Y where
  app _ x := match x with
    | .base k x => f.app k x
    | .tip x => (if ε then Y.source n else Y.target n) (e x)
    | .edge x => e x
  source_app k x := by
    cases x with
    | base _ x => exact f.source_app k x
    | tip x =>
      cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte] at he
      · change f.app k (X.source k x) = Y.source k (Y.target (k+1) (e x))
        rw [f.source_app, ← he, Y.source_source]
      · change f.app k (X.source k x) = Y.source k (Y.source (k+1) (e x))
        rw [f.source_app, ← he, Y.source_source]
    | edge x => cases ε <;> first | exact (he x).symm | rfl
  target_app k x := by
    cases x with
    | base _ x => exact f.target_app k x
    | tip x =>
      cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte] at he
      · change f.app k (X.target k x) = Y.target k (Y.target (k+1) (e x))
        rw [f.target_app, ← he, Y.target_source]
      · change f.app k (X.target k x) = Y.target k (Y.source (k+1) (e x))
        rw [f.target_app, ← he, Y.target_source]
    | edge x => cases ε <;> first | exact (he x).symm | rfl

end GlobularSet
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasColimitsOfSize.{0,v} K]
variable {D B : GlobularFrame K} {e : Hom D B}

namespace CriticalData
variable {n : ℕ} {ε : Bool} (c : CriticalData e n ε) {S : GlobularSet.{v}} {Y : K}

noncomputable def whiskerDiagram (f : GlobularSet.Hom S (D.homGlob Y))
    (a : GlobularSet.LiftStage (e.pre Y) f n) :
    GlobularSet.Hom (S.whisker n ε) (D.homGlob Y) :=
  GlobularSet.whiskerDescOriented n ε f (fun x => c.iso.inv ≫ a.app n le_rfl x) (by
    intro x
    have he := c.endpoint
    cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte] at he ⊢
    all_goals
      change _ ≫ c.iso.inv ≫ a.app n le_rfl x = f.app n x
      erw [← he, Category.assoc, Iso.hom_inv_id_assoc]
      exact a.fac n le_rfl x)

noncomputable def whiskerPresentation (S : GlobularSet.{v}) : Presentation e S n where
  obj := D.realization.obj (S.whisker n ε).presheaf
  base := (S.whiskerInclusion n ε).comp
    ((S.whisker n ε).toPresheafUnderlying.comp (D.cellMap _))
  stage := c.initialStage ((S.whisker n ε).toPresheafUnderlying.comp (D.cellMap _))
  desc f a := D.desc ((S.whisker n ε).presheafUnderlyingMap.comp (c.whiskerDiagram f a))
  base_desc f a j x := D.cell_desc (S := (S.whisker n ε).presheaf) _ j (.base j x)
  stage_desc f a j hj x := by
    by_cases h : j < n
    · let : IsIso (e.obj j) := c.low j h
      apply (cancel_epi (e.obj j)).1
      change e.obj j ≫ c.initialCell _ j hj x ≫ _ = e.obj j ≫ a.app j hj x
      rw [← Category.assoc, c.initialCell_fac]
      erw [D.cell_desc]
      exact (a.fac j hj x).symm
    · have hj' : j = n := by omega
      subst j
      change c.initialCell _ n le_rfl x ≫ _ = a.app n le_rfl x
      rw [c.initialCell_top]
      change (c.iso.hom ≫ D.cell (S.whisker n ε).presheaf (n+1) (.edge x)) ≫ _ = _
      erw [Category.assoc, D.cell_desc]
      change c.iso.hom ≫ c.iso.inv ≫ a.app n le_rfl x = _
      exact c.iso.hom_inv_id_assoc _
  hom_ext := by
    intro Y f g hb hs
    have hd := GlobularSet.whisker_hom_ext n ε
      ((S.whisker n ε).toPresheafUnderlying.comp (D.realizeHom f))
      ((S.whisker n ε).toPresheafUnderlying.comp (D.realizeHom g)) hb (by
        intro x
        have h := hs n le_rfl x
        change c.initialCell _ n le_rfl x ≫ f = c.initialCell _ n le_rfl x ≫ g at h
        rw [c.initialCell_top] at h
        change (c.iso.hom ≫ D.cell (S.whisker n ε).presheaf (n+1) (.edge x)) ≫ f =
          (c.iso.hom ≫ D.cell (S.whisker n ε).presheaf (n+1) (.edge x)) ≫ g at h
        simp only [Category.assoc] at h
        exact (cancel_epi c.iso.hom).1 h)
    apply D.hom_ext
    intro j x
    exact congrFun (congrArg (fun z => z.app j) hd) x
end CriticalData

namespace Presentation
variable (e : Hom D B) (S : GlobularSet.{v}) (m : ℕ)
variable (hm : ∀ j, m < j → IsEmpty (S.Cell j))

noncomputable def fullStage (Y : K) (f : GlobularSet.Hom S (B.homGlob Y)) :
    GlobularSet.LiftStage (e.pre Y) (f.comp (e.pre Y)) m where
  app j _ := f.app j
  source_app j _ := f.source_app j
  target_app j _ := f.target_app j
  fac _ _ _ := rfl

noncomputable def full : Presentation e S m where
  obj := B.realization.obj S.presheaf
  base := (S.toPresheafUnderlying.comp (B.cellMap _)).comp (e.pre _)
  stage := fullStage e S m _ (S.toPresheafUnderlying.comp (B.cellMap _))
  desc f a := B.desc (S.presheafUnderlyingMap.comp
    { app := fun j x => if hj : j ≤ m then a.app j hj x else (hm j (by omega)).elim x
      source_app := by
        intro j x
        by_cases h : j+1 ≤ m
        · rw [dite_eq_left (by omega), dite_eq_left h]
          exact a.source_app j h x
        · exact (hm (j+1) (by omega)).elim x
      target_app := by
        intro j x
        by_cases h : j+1 ≤ m
        · rw [dite_eq_left (by omega), dite_eq_left h]
          exact a.target_app j h x
        · exact (hm (j+1) (by omega)).elim x })
  base_desc f a j x := by
    change (e.obj j ≫ B.cell S.presheaf j x) ≫ B.desc _ = f.app j x
    erw [Category.assoc, B.cell_desc]
    by_cases hj : j ≤ m
    · dsimp only [GlobularSet.Hom.comp, GlobularSet.presheafUnderlyingMap]
      rw [dite_eq_left hj]
      exact a.fac j hj x
    · exact (hm j (by omega)).elim x
  stage_desc f a j hj x := by
    change B.cell S.presheaf j x ≫ B.desc _ = _
    erw [B.cell_desc]
    dsimp only [GlobularSet.Hom.comp, GlobularSet.presheafUnderlyingMap]
    rw [dite_eq_left hj]
    rfl
  hom_ext := by
    intro Y f g _ hs
    apply B.hom_ext
    intro j x
    by_cases hj : j ≤ m
    · exact hs j hj x
    · exact (hm j (by omega)).elim x
end Presentation
end GlobularFrame
end Grothendieck

end OAI
