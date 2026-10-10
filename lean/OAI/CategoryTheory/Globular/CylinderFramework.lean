import OAI.CategoryTheory.Globular.ReverseWhisker

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite

structure GlobularFrame (K : Type u) [Category.{v} K] where
  obj : ℕ → K
  bd : ℕ → K
  inc : ∀ j, bd j ⟶ obj j
  left : ∀ j, obj j ⟶ bd (j+1)
  right : ∀ j, obj j ⟶ bd (j+1)
  square : ∀ j, IsPushout (inc j) (inc j) (left j) (right j)
  initial : IsInitial (bd 0)

namespace GlobularFrame
variable {K : Type u} [Category.{v} K]

def diagram (B : GlobularFrame K) : CoGlobularObject K where
  obj := B.obj
  source j := B.left j ≫ B.inc (j+1)
  target j := B.right j ≫ B.inc (j+1)
  source_source j := by
    simp only [Category.assoc]
    rw [← Category.assoc (B.inc (j+1)), (B.square (j+1)).w, Category.assoc]
  target_source j := by
    simp only [Category.assoc]
    rw [← Category.assoc (B.inc (j+1)), (B.square (j+1)).w, Category.assoc]

def homGlob (B : GlobularFrame K) (Y : K) : GlobularSet.{v} where
  Cell j := B.obj j ⟶ Y
  source j f := B.diagram.source j ≫ f
  target j f := B.diagram.target j ≫ f
  source_source j f := by
    change B.diagram.source j ≫ B.diagram.source (j+1) ≫ f =
      B.diagram.source j ≫ B.diagram.target (j+1) ≫ f
    erw [← Category.assoc, B.diagram.source_source, Category.assoc]
  target_source j f := by
    change B.diagram.target j ≫ B.diagram.source (j+1) ≫ f =
      B.diagram.target j ≫ B.diagram.target (j+1) ≫ f
    erw [← Category.assoc, B.diagram.target_source, Category.assoc]

def post {B : GlobularFrame K} {X Y : K} (f : X ⟶ Y) :
    GlobularSet.Hom (B.homGlob X) (B.homGlob Y) where
  app _ a := a ≫ f
  source_app _ _ := Category.assoc _ _ _
  target_app _ _ := Category.assoc _ _ _

structure BoundaryEquiv (B : GlobularFrame K) (n : ℕ) where
  equiv : ∀ Y, (B.bd n ⟶ Y) ≃ (B.homGlob Y).Boundary n
  naturality : ∀ {X Y} (a : B.bd n ⟶ X) (f : X ⟶ Y),
    equiv Y (a ≫ f) = (post f).boundaryMap n (equiv X a)
  inc_boundary : ∀ {Y} (a : B.obj n ⟶ Y),
    equiv Y (B.inc n ≫ a) = (B.homGlob Y).boundary n a

namespace BoundaryEquiv
variable (B : GlobularFrame K)
noncomputable def zero : BoundaryEquiv B 0 where
  equiv Y :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => B.initial.to Y
      left_inv := fun _ => B.initial.hom_ext _ _
      right_inv := fun _ => by change (PUnit.unit : PUnit) = _; exact Subsingleton.elim _ _ }
  naturality _ _ := rfl
  inc_boundary _ := rfl

variable {B} {n : ℕ} (R : BoundaryEquiv B n)

def nextValue (Y : K) (f : B.bd (n+1) ⟶ Y) : (B.homGlob Y).Boundary (n+1) :=
  ⟨(B.left n ≫ f, B.right n ≫ f), by
    rw [GlobularSet.parallel_iff_boundary_eq, ← R.inc_boundary, ← R.inc_boundary,
      ← Category.assoc, ← Category.assoc, (B.square n).w]⟩

theorem nextValue_bijective (Y : K) : Function.Bijective (R.nextValue Y) := by
  constructor
  · intro f g h
    apply (B.square n).hom_ext
    · exact congrArg (fun b => b.1.1) h
    · exact congrArg (fun b => b.1.2) h
  · intro b
    have hb : B.inc n ≫ b.1.1 = B.inc n ≫ b.1.2 := by
      apply (R.equiv Y).injective
      erw [R.inc_boundary, R.inc_boundary]
      exact (GlobularSet.parallel_iff_boundary_eq _ _ _ _).1 b.2
    refine ⟨(B.square n).desc b.1.1 b.1.2 hb, ?_⟩
    apply Subtype.ext
    exact Prod.ext ((B.square n).inl_desc _ _ _) ((B.square n).inr_desc _ _ _)

noncomputable def succ : BoundaryEquiv B (n+1) where
  equiv Y := Equiv.ofBijective (R.nextValue Y) (R.nextValue_bijective Y)
  naturality a f := by
    apply Subtype.ext
    change (B.left n ≫ (a ≫ f), B.right n ≫ (a ≫ f)) =
      ((B.left n ≫ a) ≫ f, (B.right n ≫ a) ≫ f)
    exact Prod.ext (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
  inc_boundary a := by
    apply Subtype.ext
    exact Prod.ext (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

end BoundaryEquiv

noncomputable def boundaryEquiv (B : GlobularFrame K) : (n : ℕ) → BoundaryEquiv B n
  | 0 => BoundaryEquiv.zero B
  | n+1 => (boundaryEquiv B n).succ

structure Hom (D B : GlobularFrame K) where
  obj : ∀ j, D.obj j ⟶ B.obj j
  bd : ∀ j, D.bd j ⟶ B.bd j
  inc : ∀ j, bd j ≫ B.inc j = D.inc j ≫ obj j
  left : ∀ j, D.left j ≫ bd (j+1) = obj j ≫ B.left j
  right : ∀ j, D.right j ≫ bd (j+1) = obj j ≫ B.right j

namespace Hom
variable {D B : GlobularFrame K}
@[reassoc] theorem source_naturality (e : Hom D B) (j : ℕ) :
    D.diagram.source j ≫ e.obj (j+1) = e.obj j ≫ B.diagram.source j := by
  change (D.left j ≫ D.inc (j+1)) ≫ e.obj (j+1) = _
  rw [Category.assoc, ← e.inc, ← Category.assoc, e.left, Category.assoc]
  rfl
@[reassoc] theorem target_naturality (e : Hom D B) (j : ℕ) :
    D.diagram.target j ≫ e.obj (j+1) = e.obj j ≫ B.diagram.target j := by
  change (D.right j ≫ D.inc (j+1)) ≫ e.obj (j+1) = _
  rw [Category.assoc, ← e.inc, ← Category.assoc, e.right, Category.assoc]
  rfl

def pre (e : Hom D B) (Y : K) : GlobularSet.Hom (B.homGlob Y) (D.homGlob Y) where
  app j a := e.obj j ≫ a
  source_app j a := by
    change e.obj j ≫ B.diagram.source j ≫ a = D.diagram.source j ≫ e.obj (j+1) ≫ a
    erw [← Category.assoc, ← e.source_naturality, Category.assoc]
    rfl
  target_app j a := by
    change e.obj j ≫ B.diagram.target j ≫ a = D.diagram.target j ≫ e.obj (j+1) ≫ a
    erw [← Category.assoc, ← e.target_naturality, Category.assoc]
    rfl

theorem boundary_naturality (e : Hom D B) {Y : K} (j : ℕ) (a : B.bd j ⟶ Y) :
    (D.boundaryEquiv j).equiv Y (e.bd j ≫ a) =
      (e.pre Y).boundaryMap j ((B.boundaryEquiv j).equiv Y a) := by
  cases j with
  | zero => rfl
  | succ j =>
    apply Subtype.ext
    change (D.left j ≫ (e.bd (j+1) ≫ a), D.right j ≫ (e.bd (j+1) ≫ a)) =
      (e.obj j ≫ (B.left j ≫ a), e.obj j ≫ (B.right j ≫ a))
    simp only [← Category.assoc, e.left, e.right]

end Hom
end GlobularFrame

namespace GlobularSet

def fiberProd {X Y Z : GlobularSet.{v}} (f : Hom X Z) (g : Hom Y Z) : GlobularSet.{v} where
  Cell k := {xy : X.Cell k × Y.Cell k // f.app k xy.1 = g.app k xy.2}
  source k xy := ⟨(X.source k xy.1.1, Y.source k xy.1.2), by
    rw [f.source_app, g.source_app, xy.2]⟩
  target k xy := ⟨(X.target k xy.1.1, Y.target k xy.1.2), by
    rw [f.target_app, g.target_app, xy.2]⟩
  source_source k xy := Subtype.ext (Prod.ext (X.source_source k _) (Y.source_source k _))
  target_source k xy := Subtype.ext (Prod.ext (X.target_source k _) (Y.target_source k _))

namespace fiberProd
variable {X Y Z : GlobularSet.{v}} (f : Hom X Z) (g : Hom Y Z)
def fst : Hom (fiberProd f g) X where
  app _ xy := xy.1.1
  source_app _ _ := rfl
  target_app _ _ := rfl
def snd : Hom (fiberProd f g) Y where
  app _ xy := xy.1.2
  source_app _ _ := rfl
  target_app _ _ := rfl

variable {A : GlobularSet.{v}}
def lift (a : Hom A X) (b : Hom A Y) (h : a.comp f = b.comp g) : Hom A (fiberProd f g) where
  app k x := ⟨(a.app k x, b.app k x), congrFun (congrArg (fun t => t.app k) h) x⟩
  source_app k x := Subtype.ext (Prod.ext (a.source_app k x) (b.source_app k x))
  target_app k x := Subtype.ext (Prod.ext (a.target_app k x) (b.target_app k x))

@[simp] theorem lift_fst (a : Hom A X) (b : Hom A Y) (h : a.comp f = b.comp g) :
    (lift f g a b h).comp (fst f g) = a := rfl
@[simp] theorem lift_snd (a : Hom A X) (b : Hom A Y) (h : a.comp f = b.comp g) :
    (lift f g a b h).comp (snd f g) = b := rfl

end fiberProd
end GlobularSet

namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasPushouts K]
variable {D B : GlobularFrame K}

noncomputable abbrev oneSided (e : Hom D B) (j : ℕ) : K := pushout (e.bd j) (D.inc j)
noncomputable def oneSidedMap (e : Hom D B) (j : ℕ) : oneSided e j ⟶ B.obj j :=
  pushout.desc (B.inc j) (e.obj j) (e.inc j)

namespace Hom
variable (e : Hom D B) {X Y : K} (p : X ⟶ Y)

def relativeGlob : GlobularSet.{v} := GlobularSet.fiberProd (e.pre Y) (post p)

def relativeMap : GlobularSet.Hom (B.homGlob X) (e.relativeGlob p) :=
  GlobularSet.fiberProd.lift (e.pre Y) (post p) (post p) (e.pre X) (by
    ext k a
    exact (Category.assoc _ _ _).symm)

theorem relativeMap_liftsBoundary (j : ℕ) (hp : HasLiftingProperty (oneSidedMap e j) p) :
    GlobularSet.LiftsBoundary (e.relativeMap p) j := by
  intro bd z hz
  let a := (B.boundaryEquiv j).equiv X |>.symm bd
  have ha : (B.boundaryEquiv j).equiv X a = bd := Equiv.apply_symm_apply _ _
  have hz₁ := congrArg ((GlobularSet.fiberProd.fst (e.pre Y) (post p)).boundaryMap j) hz
  have hz₂ := congrArg ((GlobularSet.fiberProd.snd (e.pre Y) (post p)).boundaryMap j) hz
  have hab : e.bd j ≫ a = D.inc j ≫ z.1.2 := by
    apply ((D.boundaryEquiv j).equiv X).injective
    erw [e.boundary_naturality, ha, (D.boundaryEquiv j).inc_boundary]
    cases j with
    | zero => rfl
    | succ j => exact hz₂.symm
  have hap : a ≫ p = B.inc j ≫ z.1.1 := by
    apply ((B.boundaryEquiv j).equiv Y).injective
    erw [(B.boundaryEquiv j).naturality, ha, (B.boundaryEquiv j).inc_boundary]
    cases j with
    | zero => rfl
    | succ j => exact hz₁.symm
  let top : oneSided e j ⟶ X := pushout.desc a z.1.2 hab
  have sq : CommSq top (oneSidedMap e j) p z.1.1 := by
    constructor
    apply pushout.hom_ext
    · dsimp only [top, oneSidedMap]
      erw [pushout.inl_desc_assoc, pushout.inl_desc_assoc]
      exact hap
    · dsimp only [top, oneSidedMap]
      erw [pushout.inr_desc_assoc, pushout.inr_desc_assoc]
      exact z.2.symm
  let : sq.HasLift := hp.sq_hasLift sq
  let l := sq.lift
  refine ⟨l, ?_, ?_⟩
  · have hh : B.inc j ≫ l = a := by
      have h := congrArg (pushout.inl (e.bd j) (D.inc j) ≫ ·) sq.fac_left
      dsimp only [oneSidedMap, top] at h
      erw [pushout.inl_desc, pushout.inl_desc_assoc] at h
      exact h
    rw [← (B.boundaryEquiv j).inc_boundary, hh, ha]
  · apply Subtype.ext
    apply Prod.ext
    · exact sq.fac_right
    · have h := congrArg (pushout.inr (e.bd j) (D.inc j) ≫ ·) sq.fac_left
      dsimp only [oneSidedMap, top] at h
      erw [pushout.inr_desc, pushout.inr_desc_assoc] at h
      exact h

end Hom
end GlobularFrame

end Grothendieck

end OAI
