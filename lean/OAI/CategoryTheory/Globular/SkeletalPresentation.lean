import OAI.CategoryTheory.Globular.CylinderGluing

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularSet.LiftStage
variable {S A B : GlobularSet.{v}} {p : Hom A B} {f : Hom S B}
def restrict {n m : ℕ} (a : LiftStage p f m) (h : n ≤ m) : LiftStage p f n where
  app j hj := a.app j (hj.trans h)
  source_app j hj := a.source_app j (hj.trans h)
  target_app j hj := a.target_app j (hj.trans h)
  fac j hj := a.fac j (hj.trans h)
end GlobularSet.LiftStage
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] {D B : GlobularFrame K}
variable {e : Hom D B} {S : GlobularSet.{v}} {m : ℕ}

structure Presentation (e : Hom D B) (S : GlobularSet.{v}) (m : ℕ) where
  obj : K
  base : GlobularSet.Hom S (D.homGlob obj)
  stage : GlobularSet.LiftStage (e.pre obj) base m
  desc : ∀ {Y : K} (f : GlobularSet.Hom S (D.homGlob Y)),
    GlobularSet.LiftStage (e.pre Y) f m → (obj ⟶ Y)
  base_desc : ∀ {Y} f a j x, base.app j x ≫ desc (Y := Y) f a = f.app j x
  stage_desc : ∀ {Y} f a j hj x, stage.app j hj x ≫ desc (Y := Y) f a = a.app j hj x
  hom_ext : ∀ {Y} {f g : obj ⟶ Y},
    (∀ j x, base.app j x ≫ f = base.app j x ≫ g) →
    (∀ j hj x, stage.app j hj x ≫ f = stage.app j hj x ≫ g) → f = g

namespace Presentation
variable (V : Presentation e S m)
noncomputable def stageOn {Y : K} (f : GlobularSet.Hom S (D.homGlob Y))
    (b : V.obj ⟶ Y) (hb : ∀ j x, V.base.app j x ≫ b = f.app j x) :
    GlobularSet.LiftStage (e.pre Y) f m where
  app j hj x := V.stage.app j hj x ≫ b
  source_app j hj x := by
    change V.stage.app j _ (S.source j x) ≫ b = B.diagram.source j ≫ V.stage.app (j+1) hj x ≫ b
    erw [V.stage.source_app]
    exact Category.assoc _ _ _
  target_app j hj x := by
    change V.stage.app j _ (S.target j x) ≫ b = B.diagram.target j ≫ V.stage.app (j+1) hj x ≫ b
    erw [V.stage.target_app]
    exact Category.assoc _ _ _
  fac j hj x := by
    change e.obj j ≫ V.stage.app j hj x ≫ b = f.app j x
    have hv : e.obj j ≫ V.stage.app j hj x = V.base.app j x := V.stage.fac j hj x
    erw [← Category.assoc, hv, hb]

noncomputable def postStage {Y : K} (b : V.obj ⟶ Y) :
    GlobularSet.LiftStage (e.pre Y) (V.base.comp (post b)) m :=
  V.stageOn _ b (fun _ _ => rfl)

variable {n : ℕ} (U : Presentation e S n)
noncomputable def comparison (h : n ≤ m) : U.obj ⟶ V.obj :=
  U.desc V.base (V.stage.restrict h)

@[reassoc] theorem comparison_base (h : n ≤ m) (j : ℕ) (x : S.Cell j) :
    U.base.app j x ≫ V.comparison U h = V.base.app j x := U.base_desc _ _ j x
@[reassoc] theorem comparison_stage (h : n ≤ m) (j : ℕ) (hj : j ≤ n) (x : S.Cell j) :
    U.stage.app j hj x ≫ V.comparison U h = V.stage.app j (hj.trans h) x := U.stage_desc _ _ j hj x

variable [HasPushouts K]
theorem comparison_lifting (h : n ≤ m) {X Y : K} (p : X ⟶ Y)
    (hp : ∀ j, n < j → j ≤ m → HasLiftingProperty (oneSidedMap e j) p) :
    HasLiftingProperty (V.comparison U h) p := by
  constructor
  intro a b sq
  let f : GlobularSet.Hom S (D.homGlob X) := U.base.comp (post a)
  have hb : ∀ j x, V.base.app j x ≫ b = (f.comp (post p)).app j x := by
    intro j x
    change V.base.app j x ≫ b = (U.base.app j x ≫ a) ≫ p
    erw [Category.assoc, sq.w, ← Category.assoc, comparison_base]
  let t := V.stageOn (f.comp (post p)) b hb
  let s : RelativeStage e p f t n h :=
    ⟨U.postStage a, fun j hj x => by
      change (U.stage.app j hj x ≫ a) ≫ p = V.stage.app j (hj.trans h) x ≫ b
      erw [Category.assoc, sq.w, ← Category.assoc, comparison_stage]⟩
  let d := m-n
  have hd : n+d = m := Nat.add_sub_of_le h
  let z := s.extendBy d (by omega) (fun j hj hj' => hp j hj (by omega))
  let l := V.desc f (z.stage.restrict (by omega : m ≤ n+d))
  have hl₁ : V.comparison U h ≫ l = a := by
    apply U.hom_ext
    · intro j x
      erw [← Category.assoc, comparison_base, V.base_desc]
      rfl
    · intro j hj x
      erw [← Category.assoc, comparison_stage, V.stage_desc]
      change z.stage.app j _ x = U.stage.app j hj x ≫ a
      exact s.extendBy_old d _ _ j hj x
  have hl₂ : l ≫ p = b := by
    apply V.hom_ext
    · intro j x
      erw [← Category.assoc, V.base_desc]
      exact (hb j x).symm
    · intro j hj x
      erw [← Category.assoc, V.stage_desc]
      exact z.fac_right j (by omega) x
  exact CommSq.HasLift.mk' ⟨l, hl₁, hl₂⟩

end Presentation
end GlobularFrame
end Grothendieck

end OAI
