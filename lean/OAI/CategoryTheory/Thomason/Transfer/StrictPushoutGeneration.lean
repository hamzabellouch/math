import OAI.CategoryTheory.Thomason.Chains.SimplexBasisHeight
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

namespace OAI

section

/-!
# Fibers of actual labelled pushouts

The published input is Ara--Maltsiniotis (2014), Lemma 2.8,
arXiv:1305.5086v3, pp.14--15: either endpoint-fiber functor on the slice
over the walking arrow has a right adjoint. The consequence used is preservation of small colimits by the
concrete fiber functors. The same statement applies in every positive
finite dimension and in omega dimension.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

namespace StrictOmegaCategory

/-- The walking arrow as an actual strict positive finite category. -/
def finiteInterval (n : ℕ) : Truncated (n + 1) :=
  ⟨StrictPoset.category (Fin 2), fun x =>
    (StrictPoset.category (Fin 2)).dimensionLE_mono (by omega)
      (StrictPoset.category_isTruncated (Fin 2) x)⟩

/-- Endpoint fibers of finite strict categories, formed by the same full
subcategories of their ambient omega-categories. -/
def finiteLabelFiberFunctor (n : ℕ) (e : Fin 2) :
    Over (finiteInterval n) ⥤ Truncated (n + 1) where
  obj X := ⟨labelFiber X.hom e, labelFiber_isTruncated X.hom e X.left.property⟩
  map {X Y} f := labelFiberMap X.hom Y.hom e f.left (Over.w f)
  map_id X := by
    apply Hom.ext
    funext x
    rfl
  map_comp f g := by
    apply Hom.ext
    funext x
    rfl

end StrictOmegaCategory

/-- The small-colimit consequence of the precise published endpoint-fiber
adjunction, on the actual functors defined above. -/
structure PublishedLabelFiberInput : Prop where
  omega (e : Fin 2) :
    PreservesColimitsOfSize.{0, 0} (StrictOmegaCategory.labelFiberFunctor (Fin 2) e)
  finite (n : ℕ) (e : Fin 2) :
    PreservesColimitsOfSize.{0, 0} (StrictOmegaCategory.finiteLabelFiberFunctor n e)

namespace PublishedLabelFiberInput

variable (p : PublishedLabelFiberInput)

include p

/-- A labelled attaching pushout remains a pushout on either full endpoint fiber. -/
theorem omega_isPushout (e : Fin 2)
    {A B X Y : Over (StrictPoset.category (Fin 2))}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) :
    IsPushout ((StrictOmegaCategory.labelFiberFunctor (Fin 2) e).map i)
      ((StrictOmegaCategory.labelFiberFunctor (Fin 2) e).map a)
      ((StrictOmegaCategory.labelFiberFunctor (Fin 2) e).map b)
      ((StrictOmegaCategory.labelFiberFunctor (Fin 2) e).map j) := by
  have := p.omega e
  exact hp.map _

/-- The same statement uses genuine pushouts in the finite category. -/
theorem finite_isPushout (n : ℕ) (e : Fin 2)
    {A B X Y : Over (StrictOmegaCategory.finiteInterval n)}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) :
    IsPushout ((StrictOmegaCategory.finiteLabelFiberFunctor n e).map i)
      ((StrictOmegaCategory.finiteLabelFiberFunctor n e).map a)
      ((StrictOmegaCategory.finiteLabelFiberFunctor n e).map b)
      ((StrictOmegaCategory.finiteLabelFiberFunctor n e).map j) := by
  have := p.finite n e
  exact hp.map _

end PublishedLabelFiberInput
end Thomason.Construction

end

section

/-! # Composition generation in strict pushouts

The images of all cells in the two pieces generate their strict pushout
using composition alone. Faces introduce no extra generators because the
piece maps preserve them. The proof uses the universal property of the
pushout and a generated strict subcategory.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory CategoryTheory.Limits

namespace CompositionExpression

/-- Substitute actual expressions for the mapped generators of a strict
composition expression. -/
theorem substitute {C D : StrictOmegaCategory.{0}} {I J : Type} {g : I → C} {h : J → D}
    (F : C ⟶ D) (hh : ∀ i, Nonempty (CompositionExpression D h (F.toFun (g i))))
    {x : C} (t : CompositionExpression C g x) :
    Nonempty (CompositionExpression D h (F.toFun x)) := by
  induction t with
  | generator i => exact hh i
  | @comp x y r hxy tx ty ihx ihy =>
    have hf : D.target r (F.toFun x) = D.source r (F.toFun y) :=
      (F.map_face true r x).symm.trans
        ((congrArg F.toFun hxy).trans (F.map_face false r y))
    rw [F.map_comp r x y hxy hf]
    obtain ⟨sx⟩ := ihx
    obtain ⟨sy⟩ := ihy
    exact ⟨.comp r hf sx sy⟩

theorem face {C : StrictOmegaCategory.{0}} {I : Type} {g : I → C}
    (hface : ∀ i a n, Nonempty (CompositionExpression C g (C.face a n (g i))))
    {x : C} (t : CompositionExpression C g x) (a : Bool) (n : ℕ) :
    Nonempty (CompositionExpression C g (C.face a n x)) := by
  induction t with
  | generator i => exact hface i a n
  | @comp x y s hxy tx ty ihx ihy =>
    by_cases hns : n < s
    · rw [C.lower_face_comp a hns x y hxy]
      exact ihx
    · by_cases hne : n = s
      · subst n
        cases a
        · rw [C.source_comp]
          exact ihx
        · rw [C.target_comp]
          exact ihy
      · have hsn : s < n := by omega
        have hm : C.target s (C.face a n x) = C.source s (C.face a n y) := by
          simpa only [target, source, C.globular, hsn, ite_true] using hxy
        rw [C.face_comp a n s hsn x y hxy hm]
        obtain ⟨sx⟩ := ihx
        obtain ⟨sy⟩ := ihy
        exact ⟨.comp s hm sx sy⟩

end CompositionExpression

namespace PushoutGeneration

noncomputable section

variable {A B D : StrictOmegaCategory.{0}} (f : A ⟶ B) (g : A ⟶ D)

abbrev category : StrictOmegaCategory.{0} := pushout f g

def generators : B ⊕ D → category f g
  | .inl x => (pushout.inl f g).toFun x
  | .inr x => (pushout.inr f g).toFun x

private theorem generators_face (i : B ⊕ D) (a : Bool) (n : ℕ) :
    Nonempty (CompositionExpression (category f g) (generators f g)
      ((category f g).face a n (generators f g i))) := by
  cases i with
  | inl x =>
    change Nonempty (CompositionExpression _ _
      ((pushout f g).face a n ((pushout.inl f g).toFun x)))
    rw [← (pushout.inl f g).map_face]
    exact ⟨CompositionExpression.generator (C := category f g) (g := generators f g)
      (Sum.inl (B.face a n x))⟩
  | inr x =>
    change Nonempty (CompositionExpression _ _
      ((pushout f g).face a n ((pushout.inr f g).toFun x)))
    rw [← (pushout.inr f g).map_face]
    exact ⟨CompositionExpression.generator (C := category f g) (g := generators f g)
      (Sum.inr (D.face a n x))⟩

private def generated : StrictOmegaCategory.{0} where
  Cell := {x : category f g // Nonempty (CompositionExpression _ (generators f g) x)}
  face a n x := ⟨(pushout f g).face a n x.val, by
    obtain ⟨t⟩ := x.property
    exact t.face (generators_face f g) a n⟩
  comp n x y h := ⟨(pushout f g).comp n x.val y.val (congrArg Subtype.val h), by
    obtain ⟨tx⟩ := x.property
    obtain ⟨ty⟩ := y.property
    exact ⟨.comp n (congrArg Subtype.val h) tx ty⟩⟩
  globular a b m n x := by
    apply Subtype.ext
    exact ((pushout f g).globular a b m n x.val).trans (by split_ifs <;> rfl)
  source_comp n x y h := Subtype.ext ((pushout f g).source_comp n x.val y.val _)
  target_comp n x y h := Subtype.ext ((pushout f g).target_comp n x.val y.val _)
  face_comp a m n hnm x y h h' :=
    Subtype.ext ((pushout f g).face_comp a m n hnm x.val y.val _ _)
  left_unit n x h := Subtype.ext ((pushout f g).left_unit n x.val _)
  right_unit n x h := Subtype.ext ((pushout f g).right_unit n x.val _)
  assoc n x y z hxy hyz hl hr := Subtype.ext ((pushout f g).assoc n x.val y.val z.val _ _ _ _)
  interchange m n hmn a b c d hab hcd hac hbd hl hr :=
    Subtype.ext ((pushout f g).interchange m n hmn a.val b.val c.val d.val _ _ _ _ _ _)
  finite_dimension x := by
    obtain ⟨n, hn⟩ := (pushout f g).finite_dimension x.val
    exact ⟨n, Subtype.ext hn.1, Subtype.ext hn.2⟩

private def inclusion : generated f g ⟶ pushout f g where
  toFun := Subtype.val
  map_face _ _ _ := rfl
  map_comp _ _ _ _ _ := rfl

private def left : B ⟶ generated f g where
  toFun x := ⟨(pushout.inl f g).toFun x,
    ⟨CompositionExpression.generator (C := category f g) (g := generators f g) (Sum.inl x)⟩⟩
  map_face a n x := Subtype.ext ((pushout.inl f g).map_face a n x)
  map_comp n x y h h' := Subtype.ext ((pushout.inl f g).map_comp n x y h
    (congrArg Subtype.val h'))

private def right : D ⟶ generated f g where
  toFun x := ⟨(pushout.inr f g).toFun x,
    ⟨CompositionExpression.generator (C := category f g) (g := generators f g) (Sum.inr x)⟩⟩
  map_face a n x := Subtype.ext ((pushout.inr f g).map_face a n x)
  map_comp n x y h h' := Subtype.ext ((pushout.inr f g).map_comp n x y h
    (congrArg Subtype.val h'))

private theorem condition : f ≫ left f g = g ≫ right f g := by
  apply Hom.ext
  funext x
  apply Subtype.ext
  exact congrArg (fun h : A ⟶ pushout f g => h.toFun x) (pushout.condition (f := f) (g := g))

/-- Every actual cell in a strict pushout is a finite composite of piece cells. -/
theorem generated_by_pieces (x : category f g) :
    Nonempty (CompositionExpression _ (generators f g) x) := by
  let lift : pushout f g ⟶ generated f g := pushout.desc (left f g) (right f g) (condition f g)
  have he : lift ≫ inclusion f g = 𝟙 (pushout f g) := by
    apply pushout.hom_ext
    · change pushout.inl f g ≫ (pushout.desc (left f g) (right f g) (condition f g) ≫
        inclusion f g) = pushout.inl f g ≫ 𝟙 _
      rw [← Category.assoc, pushout.inl_desc]
      apply Hom.ext
      rfl
    · change pushout.inr f g ≫ (pushout.desc (left f g) (right f g) (condition f g) ≫
        inclusion f g) = pushout.inr f g ≫ 𝟙 _
      rw [← Category.assoc, pushout.inr_desc]
      apply Hom.ext
      rfl
  have hx : (lift.toFun x).val = x := congrArg (fun h : pushout f g ⟶ pushout f g => h.toFun x) he
  exact hx ▸ (lift.toFun x).property

end
end PushoutGeneration
end Thomason.Construction.StrictOmegaCategory

end

end OAI
