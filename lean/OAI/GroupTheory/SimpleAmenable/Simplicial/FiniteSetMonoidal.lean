import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TrajectoryStages

namespace OAI

section

section

open CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.FiniteSetGroupoid

abbrev toEquiv {U V : FiniteSetGroupoid} (f : U ⟶ V) : Fin U.size ≃ Fin V.size := f
instance {U V : FiniteSetGroupoid} : CoeFun (U ⟶ V) (fun _ => Fin U.size → Fin V.size) :=
  ⟨fun f => toEquiv f⟩
lemma hom_ext {U V : FiniteSetGroupoid} (f g : U ⟶ V) (h : ∀x,f x=g x) : f=g := Equiv.ext h
abbrev sum (U V : FiniteSetGroupoid) : FiniteSetGroupoid := ⟨U.size+V.size⟩
abbrev empty : FiniteSetGroupoid := ⟨0⟩
def sumEquiv (U V : FiniteSetGroupoid) : Fin U.size ⊕ Fin V.size ≃ Fin (sum U V).size :=
  finSumFinEquiv

def sumHom {U V W Z : FiniteSetGroupoid} (f : U ⟶ W) (g : V ⟶ Z) : sum U V ⟶ sum W Z :=
  (sumEquiv U V).symm.trans ((Equiv.sumCongr f g).trans (sumEquiv W Z))
def assoc (U V W : FiniteSetGroupoid) : sum (sum U V) W ⟶ sum U (sum V W) :=
  (sumEquiv (sum U V) W).symm.trans
    ((Equiv.sumCongr (sumEquiv U V).symm (Equiv.refl _)).trans
      ((Equiv.sumAssoc _ _ _).trans
        ((Equiv.sumCongr (Equiv.refl _) (sumEquiv V W)).trans (sumEquiv U (sum V W)))))
def swap (U V : FiniteSetGroupoid) : sum U V ⟶ sum V U :=
  (sumEquiv U V).symm.trans ((Equiv.sumComm _ _).trans (sumEquiv V U))
def left (U : FiniteSetGroupoid) : sum empty U ⟶ U :=
  (sumEquiv empty U).symm.trans (Equiv.emptySum _ _)
def right (U : FiniteSetGroupoid) : sum U empty ⟶ U :=
  (sumEquiv U empty).symm.trans (Equiv.sumEmpty _ _)
@[simp] lemma comp_eq {U V W : FiniteSetGroupoid} (f : U ⟶ V) (g : V ⟶ W) :
    (f≫g : U ⟶ W) = (toEquiv f).trans (toEquiv g) := rfl
@[simp] lemma id_eq (U : FiniteSetGroupoid) : (𝟙 U : U ⟶ U) = Equiv.refl _ := rfl
@[simp] lemma comp_apply {U V W : FiniteSetGroupoid} (f : U ⟶ V) (g : V ⟶ W) (x : Fin U.size) :
    (f≫g) x=g (f x) := rfl
@[simp] lemma id_apply (U : FiniteSetGroupoid) (x : Fin U.size) : (𝟙 U : U ⟶ U) x=x := rfl
@[simp] lemma sumHom_inl {U V W Z : FiniteSetGroupoid} (f : U ⟶ W) (g : V ⟶ Z) (x : Fin U.size) :
    sumHom f g (sumEquiv U V (.inl x))=sumEquiv W Z (.inl (f x)) := by simp [sumHom]
@[simp] lemma sumHom_inr {U V W Z : FiniteSetGroupoid} (f : U ⟶ W) (g : V ⟶ Z) (x : Fin V.size) :
    sumHom f g (sumEquiv U V (.inr x))=sumEquiv W Z (.inr (g x)) := by simp [sumHom]
@[simp] lemma assoc_left (U V W : FiniteSetGroupoid) (x : Fin U.size) :
    assoc U V W (sumEquiv (sum U V) W (.inl (sumEquiv U V (.inl x))))=
      sumEquiv U (sum V W) (.inl x) := by simp [assoc]
@[simp] lemma assoc_mid (U V W : FiniteSetGroupoid) (x : Fin V.size) :
    assoc U V W (sumEquiv (sum U V) W (.inl (sumEquiv U V (.inr x))))=
      sumEquiv U (sum V W) (.inr (sumEquiv V W (.inl x))) := by simp [assoc]
@[simp] lemma assoc_right (U V W : FiniteSetGroupoid) (x : Fin W.size) :
    assoc U V W (sumEquiv (sum U V) W (.inr x))=
      sumEquiv U (sum V W) (.inr (sumEquiv V W (.inr x))) := by simp [assoc]
@[simp] lemma swap_left (U V : FiniteSetGroupoid) (x : Fin U.size) :
    swap U V (sumEquiv U V (.inl x))=sumEquiv V U (.inr x) := by simp [swap]
@[simp] lemma swap_right (U V : FiniteSetGroupoid) (x : Fin V.size) :
    swap U V (sumEquiv U V (.inr x))=sumEquiv V U (.inl x) := by simp [swap]
@[simp] lemma left_apply (U : FiniteSetGroupoid) (x : Fin U.size) :
    left U (sumEquiv empty U (.inr x))=x := by simp [left]
@[simp] lemma right_apply (U : FiniteSetGroupoid) (x : Fin U.size) :
    right U (sumEquiv U empty (.inl x))=x := by simp [right]
lemma sumHom_id (U V : FiniteSetGroupoid) : sumHom (𝟙 U) (𝟙 V)=𝟙 (sum U V) := by
  apply hom_ext; intro x
  obtain ⟨x,rfl⟩ := (sumEquiv U V).surjective x
  cases x <;> simp [toEquiv,sumHom]
lemma sumHom_comp {U V W X Y Z : FiniteSetGroupoid} (f : U ⟶ V) (f' : V ⟶ W)
    (g : X ⟶ Y) (g' : Y ⟶ Z) : sumHom (f≫f') (g≫g')=sumHom f g ≫ sumHom f' g' := by
  apply hom_ext; intro x
  obtain ⟨x,rfl⟩ := (sumEquiv U X).surjective x
  cases x <;> simp [toEquiv,sumHom]

noncomputable abbrev monoidalStruct : MonoidalCategoryStruct FiniteSetGroupoid where
  tensorObj := sum
  tensorHom := sumHom
  whiskerLeft U _ _ f := sumHom (𝟙 U) f
  whiskerRight f U := sumHom f (𝟙 U)
  tensorUnit := empty
  associator U V W := asIso (assoc U V W)
  leftUnitor U := asIso (left U)
  rightUnitor U := asIso (right U)

attribute [instance] monoidalStruct

noncomputable instance monoidal : MonoidalCategory FiniteSetGroupoid :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := sumHom_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' => (sumHom_comp f f' g g').symm)
    (associator_naturality := by
      intro U V W U' V' W' f g h
      change sumHom (sumHom f g) h ≫ assoc U' V' W' = assoc U V W ≫ sumHom f (sumHom g h)
      apply hom_ext;intro x
      obtain ⟨y,rfl⟩ := (sumEquiv (sum U V) W).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumEquiv U V).surjective y
        cases z <;> simp [toEquiv,sumHom,assoc]
      | inr y => simp [toEquiv,sumHom,assoc])
    (leftUnitor_naturality := by
      intro U V f
      change sumHom (𝟙 empty) f ≫ left V = left U ≫ f
      apply hom_ext;intro x
      obtain ⟨y,rfl⟩ := (sumEquiv empty U).surjective x
      cases y with
      | inl y => exact isEmptyElim y
      | inr y => simp [toEquiv,sumHom,left])
    (rightUnitor_naturality := by
      intro U V f
      change sumHom f (𝟙 empty) ≫ right V = right U ≫ f
      apply hom_ext;intro x
      obtain ⟨y,rfl⟩ := (sumEquiv U empty).surjective x
      cases y with
      | inl y => simp [toEquiv,sumHom,right]
      | inr y => exact isEmptyElim y)
    (pentagon := by
      intro U V W Z
      change sumHom (assoc U V W) (𝟙 Z) ≫ assoc U (sum V W) Z ≫ sumHom (𝟙 U) (assoc V W Z) =
        assoc (sum U V) W Z ≫ assoc U V (sum W Z)
      apply hom_ext;intro x
      obtain ⟨y,rfl⟩ := (sumEquiv (sum (sum U V) W) Z).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumEquiv (sum U V) W).surjective y
        cases z with
        | inl z =>
          obtain ⟨t,rfl⟩ := (sumEquiv U V).surjective z
          cases t <;> simp [toEquiv,sumHom,assoc]
        | inr z => simp [toEquiv,sumHom,assoc]
      | inr y => simp [toEquiv,sumHom,assoc])
    (triangle := by
      intro U V
      change assoc U empty V ≫ sumHom (𝟙 U) (left V) = sumHom (right U) (𝟙 V)
      apply hom_ext;intro x
      obtain ⟨y,rfl⟩ := (sumEquiv (sum U empty) V).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumEquiv U empty).surjective y
        cases z with
        | inl z => simp [toEquiv,sumHom,assoc,left,right]
        | inr z => exact isEmptyElim z
      | inr y => simp [toEquiv,sumHom,assoc,left,right])

@[simp] theorem assoc_symm_left (U V W : FiniteSetGroupoid) (x : Fin U.size) :
    (toEquiv (assoc U V W)).symm (sumEquiv U (sum V W) (.inl x))=
      sumEquiv (sum U V) W (.inl (sumEquiv U V (.inl x))) :=
  (Equiv.symm_apply_eq _).mpr (assoc_left U V W x).symm
@[simp] theorem assoc_symm_mid (U V W : FiniteSetGroupoid) (x : Fin V.size) :
    (toEquiv (assoc U V W)).symm (sumEquiv U (sum V W) (.inr (sumEquiv V W (.inl x))))=
      sumEquiv (sum U V) W (.inl (sumEquiv U V (.inr x))) :=
  (Equiv.symm_apply_eq _).mpr (assoc_mid U V W x).symm
@[simp] theorem assoc_symm_right (U V W : FiniteSetGroupoid) (x : Fin W.size) :
    (toEquiv (assoc U V W)).symm (sumEquiv U (sum V W) (.inr (sumEquiv V W (.inr x))))=
      sumEquiv (sum U V) W (.inr x) :=
  (Equiv.symm_apply_eq _).mpr (assoc_right U V W x).symm

@[simp] theorem associator_inv_apply (U V W : FiniteSetGroupoid) (x : Fin (sum U (sum V W)).size) :
    (monoidalStruct.associator U V W).inv x=(toEquiv (assoc U V W)).symm x := by
  change (CategoryTheory.inv (assoc U V W)) x=_
  rw [← Groupoid.inv_eq_inv]
  rfl

@[simp] theorem inv_arrow_apply {U V : FiniteSetGroupoid} (f : U ⟶ V) (x : Fin V.size) :
    (CategoryTheory.inv f) x = (toEquiv f).symm x := by
  rw [← Groupoid.inv_eq_inv]
  rfl

@[simp] lemma inv_eq {U V : FiniteSetGroupoid} (f : U ⟶ V) :
    (CategoryTheory.inv f : V ⟶ U) = (toEquiv f).symm := by
  rw [← Groupoid.inv_eq_inv]
  rfl

noncomputable instance braided : BraidedCategory FiniteSetGroupoid where
  braiding U V := asIso (swap U V)
  braiding_naturality_right := by
    intro U V W f
    change sumHom (𝟙 U) f ≫ swap U W = swap U V ≫ sumHom f (𝟙 U)
    apply hom_ext;intro x
    obtain ⟨y,rfl⟩ := (sumEquiv U V).surjective x
    cases y <;> simp [toEquiv,sumHom,swap]
  braiding_naturality_left := by
    intro U V f W
    change sumHom f (𝟙 W) ≫ swap V W = swap U W ≫ sumHom (𝟙 W) f
    apply hom_ext;intro x
    obtain ⟨y,rfl⟩ := (sumEquiv U W).surjective x
    cases y <;> simp [toEquiv,sumHom,swap]
  hexagon_forward := by
    intro U V W
    change assoc U V W ≫ swap U (sum V W) ≫ assoc V W U =
      sumHom (swap U V) (𝟙 W) ≫ assoc V U W ≫ sumHom (𝟙 V) (swap U W)
    apply hom_ext;intro x
    obtain ⟨y,rfl⟩ := (sumEquiv (sum U V) W).surjective x
    cases y with
    | inl y =>
      obtain ⟨z,rfl⟩ := (sumEquiv U V).surjective y
      cases z <;> simp [toEquiv,sumHom,assoc,swap]
    | inr y => simp [toEquiv,sumHom,assoc,swap]
  hexagon_reverse := by
    intro U V W
    change (CategoryTheory.inv (assoc U V W)) ≫ swap (sum U V) W ≫ (CategoryTheory.inv (assoc W U V)) =
      sumHom (𝟙 U) (swap V W) ≫ (CategoryTheory.inv (assoc U W V)) ≫ sumHom (swap U W) (𝟙 V)
    apply hom_ext;intro x
    obtain ⟨y,rfl⟩ := (sumEquiv U (sum V W)).surjective x
    cases y with
    | inl y => simp [toEquiv,sumHom,assoc,swap]
    | inr y =>
      obtain ⟨z,rfl⟩ := (sumEquiv V W).surjective y
      cases z <;> simp [toEquiv,sumHom,assoc,swap]

noncomputable instance symmetric : SymmetricCategory FiniteSetGroupoid where
  symmetry U V := by
    change swap U V ≫ swap V U = 𝟙 (sum U V)
    apply hom_ext;intro x
    obtain ⟨y,rfl⟩ := (sumEquiv U V).surjective x
    cases y <;> simp [toEquiv,swap]

end SimpleAmenable.PolygonObject.FiniteSetGroupoid

end

end

end OAI
