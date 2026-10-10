import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.FiniteSetMonoidal
import OAI.GroupTheory.SimpleAmenable.Configurations.CellFunctor

namespace OAI

section
open CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled.Cell

variable {a n : ℕ} (P : polygonAlgebra a) (l : LabelledStage.ReducedLabel n)
lemma track_ext {U V : Labelled a n} (f g : U ⟶ V)
    (h : ∀x, (f.arrow.toEquiv x).val.1=(g.arrow.toEquiv x).val.1) : f=g := by
  apply Hom.ext; apply Arrow.ext; apply Equiv.ext; intro x
  apply Subtype.ext; exact Prod.ext (h x) ((f.positional x).trans (g.positional x).symm)

@[simp] lemma whiskerRight_arrow {U V : Labelled a n} (f : U ⟶ V) (W : Labelled a n) :
    (f ▷ W).arrow=sumArrow f.arrow (𝟙 W.polygon) := rfl
@[simp] lemma whiskerLeft_arrow (W : Labelled a n) {U V : Labelled a n} (f : U ⟶ V) :
    (W ◁ f).arrow=sumArrow (𝟙 W.polygon) f.arrow := rfl

lemma tensor_natural {U V W X : FiniteSetGroupoid} (f : U ⟶ W) (g : V ⟶ X) :
    sumHom (arrow P l f) (arrow P l g) ≫ tensorArrow P l W X =
      tensorArrow P l U V ≫ arrow P l (FiniteSetGroupoid.sumHom f g) := by
  apply track_ext; intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv (object P l U).polygon (object P l V).polygon).surjective x
  cases y with
  | inl y =>
    change ((sumArrow (arrow P l f).arrow (arrow P l g).arrow).toEquiv (sumPointEquiv _ _ (.inl y))).val.1 =
      FiniteSetGroupoid.sumHom f g (FiniteSetGroupoid.sumEquiv U V (.inl y.val.1))
    erw [sumArrow_inl,sumPointEquiv_inl,FiniteSetGroupoid.sumHom_inl]
    rfl
  | inr y =>
    change ((sumArrow (arrow P l f).arrow (arrow P l g).arrow).toEquiv (sumPointEquiv _ _ (.inr y))).val.1 =
      FiniteSetGroupoid.sumHom f g (FiniteSetGroupoid.sumEquiv U V (.inr y.val.1))
    erw [sumArrow_inr,sumPointEquiv_inr,FiniteSetGroupoid.sumHom_inr]
    rfl

lemma tensor_assoc (U V W : FiniteSetGroupoid) :
    tensorArrow P l U V ▷ object P l W ≫ tensorArrow P l (U⊗V) W ≫
        (functor P l).map (α_ U V W).hom =
      (α_ (object P l U) (object P l V) (object P l W)).hom ≫
        object P l U ◁ tensorArrow P l V W ≫ tensorArrow P l U (V⊗W) := by
  apply track_ext; intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv (sum (object P l U) (object P l V)).polygon (object P l W).polygon).surjective x
  cases y with
  | inl y =>
    obtain ⟨z,rfl⟩ := (sumPointEquiv (object P l U).polygon (object P l V).polygon).surjective y
    cases z with
    | inl z =>
      change FiniteSetGroupoid.assoc U V W _ =
        ((sumArrow (𝟙 (object P l U).polygon) (tensorArrow P l V W).arrow).toEquiv ((sumAssoc (object P l U).polygon (object P l V).polygon (object P l W).polygon).toEquiv _)).val.1
      rw [whiskerRight_arrow,sumAssoc_apply,sumAssocEquiv_left]
      erw [tensorArrow_apply,sumArrow_inl,sumPointEquiv_inl,tensorArrow_apply,
        sumPointEquiv_inl,sumArrow_inl,sumPointEquiv_inl,arrow_id_apply]
      change FiniteSetGroupoid.assoc U V W
        (FiniteSetGroupoid.sumEquiv (U⊗V) W (.inl (FiniteSetGroupoid.sumEquiv U V (.inl z.val.1)))) = _
      erw [FiniteSetGroupoid.assoc_left]
      rfl
    | inr z =>
      change FiniteSetGroupoid.assoc U V W _ =
        ((sumArrow (𝟙 (object P l U).polygon) (tensorArrow P l V W).arrow).toEquiv ((sumAssoc (object P l U).polygon (object P l V).polygon (object P l W).polygon).toEquiv _)).val.1
      rw [whiskerRight_arrow,sumAssoc_apply,sumAssocEquiv_mid]
      erw [tensorArrow_apply,sumArrow_inl,sumPointEquiv_inl,tensorArrow_apply,
        sumPointEquiv_inr,sumArrow_inr,sumPointEquiv_inr,tensorArrow_apply,sumPointEquiv_inl]
      change FiniteSetGroupoid.assoc U V W
        (FiniteSetGroupoid.sumEquiv (U⊗V) W (.inl (FiniteSetGroupoid.sumEquiv U V (.inr z.val.1)))) = _
      erw [FiniteSetGroupoid.assoc_mid]
      rfl
  | inr y =>
    change FiniteSetGroupoid.assoc U V W _ =
      ((sumArrow (𝟙 (object P l U).polygon) (tensorArrow P l V W).arrow).toEquiv ((sumAssoc (object P l U).polygon (object P l V).polygon (object P l W).polygon).toEquiv _)).val.1
    rw [whiskerRight_arrow,sumAssoc_apply,sumAssocEquiv_right]
    erw [tensorArrow_apply,sumArrow_inr,sumPointEquiv_inr,arrow_id_apply,
      sumArrow_inr,sumPointEquiv_inr,tensorArrow_apply,sumPointEquiv_inr]
    change FiniteSetGroupoid.assoc U V W
      (FiniteSetGroupoid.sumEquiv (U⊗V) W (.inr y.val.1)) = _
    erw [FiniteSetGroupoid.assoc_right]
    rfl

lemma unit_left (U : FiniteSetGroupoid) :
    (λ_ (object P l U)).hom = unitArrow P l ▷ object P l U ≫
      tensorArrow P l (𝟙_ _) U ≫ (functor P l).map (λ_ U).hom := by
  apply track_ext; intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv PolygonObject.empty (object P l U).polygon).surjective x
  cases y with
  | inl y => exact isEmptyElim y
  | inr y =>
    change ((leftUnit _).toEquiv (sumPointEquiv _ _ (.inr y))).val.1 = FiniteSetGroupoid.left U _
    simp only [leftUnit_apply,leftUnitEquiv_apply]
    change y.val.1 = FiniteSetGroupoid.left U
      ((sumArrow (unitArrow P l).arrow (𝟙 (object P l U).polygon)).toEquiv
        (sumPointEquiv PolygonObject.empty (object P l U).polygon (.inr y))).val.1
    erw [sumArrow_inr,arrow_id_apply,sumPointEquiv_inr]
    change y.val.1 = FiniteSetGroupoid.left U (FiniteSetGroupoid.sumEquiv _ _ (.inr y.val.1))
    rw [FiniteSetGroupoid.left_apply]
lemma unit_right (U : FiniteSetGroupoid) :
    (ρ_ (object P l U)).hom = object P l U ◁ unitArrow P l ≫
      tensorArrow P l U (𝟙_ _) ≫ (functor P l).map (ρ_ U).hom := by
  apply track_ext; intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv (object P l U).polygon PolygonObject.empty).surjective x
  cases y with
  | inl y =>
    change ((rightUnit _).toEquiv (sumPointEquiv _ _ (.inl y))).val.1 = FiniteSetGroupoid.right U _
    simp only [rightUnit_apply,rightUnitEquiv_apply]
    change y.val.1 = FiniteSetGroupoid.right U
      ((sumArrow (𝟙 (object P l U).polygon) (unitArrow P l).arrow).toEquiv
        (sumPointEquiv (object P l U).polygon PolygonObject.empty (.inl y))).val.1
    erw [sumArrow_inl,arrow_id_apply,sumPointEquiv_inl]
    change y.val.1 = FiniteSetGroupoid.right U (FiniteSetGroupoid.sumEquiv _ _ (.inl y.val.1))
    rw [FiniteSetGroupoid.right_apply]
  | inr y => exact isEmptyElim y

noncomputable instance cellMonoidal : (functor P l).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := asIso (X := 𝟙_ (Labelled a n))
      (Y := object P l (𝟙_ FiniteSetGroupoid)) (unitArrow P l)
    μIso U V := asIso (X := object P l U ⊗ object P l V)
      (Y := object P l (U ⊗ V)) (tensorArrow P l U V)
    μIso_hom_natural_left := by
      intro U V f W
      have h := tensor_natural P l f (𝟙 W)
      rw [show arrow P l (𝟙 W)=𝟙 _ from (functor P l).map_id W] at h
      exact h
    μIso_hom_natural_right := by
      intro U V W f
      have h := tensor_natural P l (𝟙 W) f
      rw [show arrow P l (𝟙 W)=𝟙 _ from (functor P l).map_id W] at h
      exact h
    associativity := tensor_assoc P l
    left_unitality := unit_left P l
    right_unitality := unit_right P l }
noncomputable instance cellBraided : (functor P l).Braided where
  braided U V := by
    apply track_ext; intro x
    change FiniteSetGroupoid.swap U V x.val.1 =
      ((sumSwap (object P l U).polygon (object P l V).polygon).toEquiv x).val.1
    obtain ⟨y,rfl⟩ := (sumPointEquiv (object P l U).polygon (object P l V).polygon).surjective x
    cases y with
    | inl y =>
      rw [sumSwap_apply,sumSwapEquiv_inl,sumPointEquiv_inl,sumPointEquiv_inr]
      exact FiniteSetGroupoid.swap_left U V y.val.1
    | inr y =>
      rw [sumSwap_apply,sumSwapEquiv_inr,sumPointEquiv_inr,sumPointEquiv_inl]
      exact FiniteSetGroupoid.swap_right U V y.val.1
end SimpleAmenable.PolygonObject.Labelled.Cell

end

end OAI
