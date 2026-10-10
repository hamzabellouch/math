import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonObjectSum

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section PolygonMonoidalData

open Classical Set CategoryTheory
namespace PolygonObject
variable {a : ℕ}

noncomputable def relabelArrow {U V : PolygonObject a} (e : U.Point ≃ V.Point)
    (r : Fin U.tracks → Fin V.tracks)
    (he : ∀x,(e x).val=(r x.val.1,x.val.2)) : U ⟶ V where
  toEquiv := e
  hasTable := by
    let c : Fin U.tracks → Chart (a:=a) U.tracks V.tracks := fun i => ⟨i,r i,0,U.cell i⟩
    refine ⟨Finset.univ.image c,?_,?_⟩
    · intro d hd
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
      intro x hx
      exact ⟨hx,by simpa [c,translate_zero] using he ⟨(i,x),hx⟩⟩
    · intro x
      exact ⟨c x.val.1,Finset.mem_image_of_mem c (Finset.mem_univ _),rfl,x.property⟩

noncomputable def sumSwapEquiv (U V : PolygonObject a) : (sum U V).Point ≃ (sum V U).Point :=
  (sumPointEquiv U V).symm.trans ((Equiv.sumComm _ _).trans (sumPointEquiv V U))

@[simp] theorem sumSwapEquiv_inl (U V : PolygonObject a) (x : U.Point) :
    sumSwapEquiv U V (sumPointEquiv U V (.inl x))=sumPointEquiv V U (.inr x) := by
  simp [sumSwapEquiv]
@[simp] theorem sumSwapEquiv_inr (U V : PolygonObject a) (x : V.Point) :
    sumSwapEquiv U V (sumPointEquiv U V (.inr x))=sumPointEquiv V U (.inl x) := by
  simp [sumSwapEquiv]
noncomputable def sumSwap (U V : PolygonObject a) : sum U V ⟶ sum V U :=
  relabelArrow (sumSwapEquiv U V)
    (Fin.addCases (fun i => i.natAdd V.tracks) (fun i => i.castAdd U.tracks)) (by
      intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
      cases y with
      | inl y =>
        simp only [sumSwapEquiv_inl,sumPointEquiv_inl,sumPointEquiv_inr]
        erw [Fin.addCases_left]
        rfl
      | inr y =>
        simp only [sumSwapEquiv_inr,sumPointEquiv_inl,sumPointEquiv_inr]
        erw [Fin.addCases_right]
        rfl)

noncomputable def sumAssocEquiv (U V W : PolygonObject a) : (sum (sum U V) W).Point ≃ (sum U (sum V W)).Point :=
  (sumPointEquiv (sum U V) W).symm.trans
    ((Equiv.sumCongr (sumPointEquiv U V).symm (Equiv.refl _)).trans
      ((Equiv.sumAssoc U.Point V.Point W.Point).trans
        ((Equiv.sumCongr (Equiv.refl _) (sumPointEquiv V W)).trans (sumPointEquiv U (sum V W)))))

@[simp] theorem sumAssocEquiv_left (U V W : PolygonObject a) (x : U.Point) :
    sumAssocEquiv U V W (sumPointEquiv (sum U V) W (.inl (sumPointEquiv U V (.inl x))))=
      sumPointEquiv U (sum V W) (.inl x) := by simp [sumAssocEquiv]
@[simp] theorem sumAssocEquiv_mid (U V W : PolygonObject a) (x : V.Point) :
    sumAssocEquiv U V W (sumPointEquiv (sum U V) W (.inl (sumPointEquiv U V (.inr x))))=
      sumPointEquiv U (sum V W) (.inr (sumPointEquiv V W (.inl x))) := by simp [sumAssocEquiv]
@[simp] theorem sumAssocEquiv_right (U V W : PolygonObject a) (x : W.Point) :
    sumAssocEquiv U V W (sumPointEquiv (sum U V) W (.inr x))=
      sumPointEquiv U (sum V W) (.inr (sumPointEquiv V W (.inr x))) := by simp [sumAssocEquiv]
noncomputable def sumAssoc (U V W : PolygonObject a) : sum (sum U V) W ⟶ sum U (sum V W) :=
  relabelArrow (sumAssocEquiv U V W)
    (Fin.addCases
      (Fin.addCases (fun i => i.castAdd (V.tracks+W.tracks)) (fun i => (i.castAdd W.tracks).natAdd U.tracks))
      (fun i => (i.natAdd V.tracks).natAdd U.tracks)) (by
      intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv (sum U V) W).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumPointEquiv U V).surjective y
        cases z with
        | inl z =>
          simp only [sumAssocEquiv_left,sumPointEquiv_inl]
          erw [Fin.addCases_left,Fin.addCases_left]
          rfl
        | inr z =>
          simp only [sumAssocEquiv_mid,sumPointEquiv_inl,sumPointEquiv_inr]
          erw [Fin.addCases_left,Fin.addCases_right]
          rfl
      | inr y =>
        simp only [sumAssocEquiv_right,sumPointEquiv_inr]
        erw [Fin.addCases_right]
        rfl)

noncomputable def empty : PolygonObject a := ⟨0,Fin.elim0⟩
instance : IsEmpty (empty (a:=a)).Point := ⟨fun x => Fin.elim0 x.val.1⟩

noncomputable def leftUnitEquiv (U : PolygonObject a) : (sum empty U).Point ≃ U.Point :=
  (sumPointEquiv empty U).symm.trans (Equiv.emptySum _ _)
noncomputable def rightUnitEquiv (U : PolygonObject a) : (sum U empty).Point ≃ U.Point :=
  (sumPointEquiv U empty).symm.trans (Equiv.sumEmpty _ _)

@[simp] theorem leftUnitEquiv_apply (U : PolygonObject a) (x : U.Point) :
    leftUnitEquiv U (sumPointEquiv empty U (.inr x))=x := by simp [leftUnitEquiv]
@[simp] theorem rightUnitEquiv_apply (U : PolygonObject a) (x : U.Point) :
    rightUnitEquiv U (sumPointEquiv U empty (.inl x))=x := by simp [rightUnitEquiv]
noncomputable def leftUnit (U : PolygonObject a) : sum empty U ⟶ U :=
  relabelArrow (leftUnitEquiv U) (Fin.addCases Fin.elim0 id) (by
    intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv empty U).surjective x
    cases y with
    | inl y => exact isEmptyElim y
    | inr y =>
      simp only [leftUnitEquiv_apply,sumPointEquiv_inr]
      erw [Fin.addCases_right]
      rfl)
noncomputable def rightUnit (U : PolygonObject a) : sum U empty ⟶ U :=
  relabelArrow (rightUnitEquiv U) (Fin.addCases id Fin.elim0) (by
    intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv U empty).surjective x
    cases y with
    | inl y =>
      simp only [rightUnitEquiv_apply,sumPointEquiv_inl]
      erw [Fin.addCases_left]
      rfl
    | inr y => exact isEmptyElim y)

@[simp] theorem sumSwap_apply (U V : PolygonObject a) (x : (sum U V).Point) :
    (sumSwap U V).toEquiv x=sumSwapEquiv U V x := rfl
@[simp] theorem sumAssoc_apply (U V W : PolygonObject a) (x : (sum (sum U V) W).Point) :
    (sumAssoc U V W).toEquiv x=sumAssocEquiv U V W x := rfl
@[simp] theorem leftUnit_apply (U : PolygonObject a) (x : (sum empty U).Point) :
    (leftUnit U).toEquiv x=leftUnitEquiv U x := rfl
@[simp] theorem rightUnit_apply (U : PolygonObject a) (x : (sum U empty).Point) :
    (rightUnit U).toEquiv x=rightUnitEquiv U x := rfl

end PolygonObject
end PolygonMonoidalData

open Classical CategoryTheory
namespace PolygonObject
variable {a : ℕ}

noncomputable abbrev monoidalStruct : MonoidalCategoryStruct (PolygonObject a) where
  tensorObj := sum
  tensorHom := sumArrow
  whiskerLeft U _ _ f := sumArrow (𝟙 U) f
  whiskerRight f U := sumArrow f (𝟙 U)
  tensorUnit := empty
  associator U V W := asIso (sumAssoc U V W)
  leftUnitor U := asIso (leftUnit U)
  rightUnitor U := asIso (rightUnit U)

attribute [instance] monoidalStruct

noncomputable instance monoidal : MonoidalCategory (PolygonObject a) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := sumArrow_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' => (sumArrow_comp f f' g g').symm)
    (associator_naturality := by
      intro U V W U' V' W' f g h
      change sumArrow (sumArrow f g) h ≫ sumAssoc U' V' W' = sumAssoc U V W ≫ sumArrow f (sumArrow g h)
      apply Arrow.ext;apply Equiv.ext;intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv (sum U V) W).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumPointEquiv U V).surjective y
        cases z <;> simp
      | inr y => simp)
    (leftUnitor_naturality := by
      intro U V f
      change sumArrow (𝟙 empty) f ≫ leftUnit V = leftUnit U ≫ f
      apply Arrow.ext;apply Equiv.ext;intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv empty U).surjective x
      cases y with
      | inl y => exact isEmptyElim y
      | inr y => simp)
    (rightUnitor_naturality := by
      intro U V f
      change sumArrow f (𝟙 empty) ≫ rightUnit V = rightUnit U ≫ f
      apply Arrow.ext;apply Equiv.ext;intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv U empty).surjective x
      cases y with
      | inl y => simp
      | inr y => exact isEmptyElim y)
    (pentagon := by
      intro U V W Z
      change sumArrow (sumAssoc U V W) (𝟙 Z) ≫ sumAssoc U (sum V W) Z ≫ sumArrow (𝟙 U) (sumAssoc V W Z) =
        sumAssoc (sum U V) W Z ≫ sumAssoc U V (sum W Z)
      apply Arrow.ext;apply Equiv.ext;intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv (sum (sum U V) W) Z).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumPointEquiv (sum U V) W).surjective y
        cases z with
        | inl z =>
          obtain ⟨t,rfl⟩ := (sumPointEquiv U V).surjective z
          cases t <;> simp
        | inr z => simp
      | inr y => simp)
    (triangle := by
      intro U V
      change sumAssoc U empty V ≫ sumArrow (𝟙 U) (leftUnit V) = sumArrow (rightUnit U) (𝟙 V)
      apply Arrow.ext;apply Equiv.ext;intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv (sum U empty) V).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumPointEquiv U empty).surjective y
        cases z with
        | inl z => simp
        | inr z => exact isEmptyElim z
      | inr y => simp)

@[simp] theorem sumAssocEquiv_symm_left (U V W : PolygonObject a) (x : U.Point) :
    (sumAssocEquiv U V W).symm (sumPointEquiv U (sum V W) (.inl x))=
      sumPointEquiv (sum U V) W (.inl (sumPointEquiv U V (.inl x))) :=
  (Equiv.symm_apply_eq _).mpr (sumAssocEquiv_left U V W x).symm
@[simp] theorem sumAssocEquiv_symm_mid (U V W : PolygonObject a) (x : V.Point) :
    (sumAssocEquiv U V W).symm (sumPointEquiv U (sum V W) (.inr (sumPointEquiv V W (.inl x))))=
      sumPointEquiv (sum U V) W (.inl (sumPointEquiv U V (.inr x))) :=
  (Equiv.symm_apply_eq _).mpr (sumAssocEquiv_mid U V W x).symm
@[simp] theorem sumAssocEquiv_symm_right (U V W : PolygonObject a) (x : W.Point) :
    (sumAssocEquiv U V W).symm (sumPointEquiv U (sum V W) (.inr (sumPointEquiv V W (.inr x))))=
      sumPointEquiv (sum U V) W (.inr x) :=
  (Equiv.symm_apply_eq _).mpr (sumAssocEquiv_right U V W x).symm

@[simp] theorem associator_inv_apply (U V W : PolygonObject a) (x : (sum U (sum V W)).Point) :
    (monoidalStruct.associator U V W).inv.toEquiv x=(sumAssocEquiv U V W).symm x := by
  change (CategoryTheory.inv (sumAssoc U V W)).toEquiv x=_
  rw [← Groupoid.inv_eq_inv]
  rfl

@[simp] theorem sumAssoc_toEquiv (U V W : PolygonObject a) :
    (sumAssoc U V W).toEquiv = sumAssocEquiv U V W := rfl

@[simp] theorem inv_arrow_apply {U V : PolygonObject a} (f : U ⟶ V) (x : V.Point) :
    (CategoryTheory.inv f).toEquiv x = f.toEquiv.symm x := by
  rw [← Groupoid.inv_eq_inv]
  rfl

noncomputable instance braided : BraidedCategory (PolygonObject a) where
  braiding U V := asIso (sumSwap U V)
  braiding_naturality_right := by
    intro U V W f
    change sumArrow (𝟙 U) f ≫ sumSwap U W = sumSwap U V ≫ sumArrow f (𝟙 U)
    apply Arrow.ext;apply Equiv.ext;intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
    cases y <;> simp
  braiding_naturality_left := by
    intro U V f W
    change sumArrow f (𝟙 W) ≫ sumSwap V W = sumSwap U W ≫ sumArrow (𝟙 W) f
    apply Arrow.ext;apply Equiv.ext;intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv U W).surjective x
    cases y <;> simp
  hexagon_forward := by
    intro U V W
    change sumAssoc U V W ≫ sumSwap U (sum V W) ≫ sumAssoc V W U =
      sumArrow (sumSwap U V) (𝟙 W) ≫ sumAssoc V U W ≫ sumArrow (𝟙 V) (sumSwap U W)
    apply Arrow.ext;apply Equiv.ext;intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv (sum U V) W).surjective x
    cases y with
    | inl y =>
      obtain ⟨z,rfl⟩ := (sumPointEquiv U V).surjective y
      cases z <;> simp
    | inr y => simp
  hexagon_reverse := by
    intro U V W
    change (CategoryTheory.inv (sumAssoc U V W)) ≫ sumSwap (sum U V) W ≫ (CategoryTheory.inv (sumAssoc W U V)) =
      sumArrow (𝟙 U) (sumSwap V W) ≫ (CategoryTheory.inv (sumAssoc U W V)) ≫ sumArrow (sumSwap U W) (𝟙 V)
    apply Arrow.ext;apply Equiv.ext;intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv U (sum V W)).surjective x
    cases y with
    | inl y => simp only [arrow_comp_apply, inv_arrow_apply, sumAssoc_toEquiv,
        sumAssocEquiv_symm_left,sumAssocEquiv_symm_mid,
        sumSwap_apply,sumSwapEquiv_inl,sumArrow_inl,arrow_id_apply]
    | inr y =>
      obtain ⟨z,rfl⟩ := (sumPointEquiv V W).surjective y
      cases z <;> simp only [arrow_comp_apply, inv_arrow_apply, sumAssoc_toEquiv,
        sumAssocEquiv_symm_left,sumAssocEquiv_symm_mid,sumAssocEquiv_symm_right,
        sumSwap_apply,sumSwapEquiv_inl,sumSwapEquiv_inr,sumArrow_inl,sumArrow_inr,arrow_id_apply]

noncomputable instance symmetric : SymmetricCategory (PolygonObject a) where
  symmetry U V := by
    change sumSwap U V ≫ sumSwap V U = 𝟙 (sum U V)
    apply Arrow.ext;apply Equiv.ext;intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
    cases y <;> simp

end PolygonObject

end SimpleAmenable

end OAI
