import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.BooleanStages

namespace OAI

section

section

open CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject

namespace Labelled
variable {a n : ℕ}

noncomputable abbrev sum (U V : Labelled a n) : Labelled a n where
  polygon := PolygonObject.sum U.polygon V.polygon
  label := Fin.addCases U.label V.label
  reduced j i := by
    refine Fin.addCases ?_ ?_ j
    · intro k; simpa only [Fin.addCases_left] using U.reduced k i
    · intro k; simpa only [Fin.addCases_right] using V.reduced k i

noncomputable abbrev empty : Labelled a n where
  polygon := PolygonObject.empty
  label := Fin.elim0
  reduced := fun j => Fin.elim0 j

@[simp] lemma sum_label_left (U V : Labelled a n) (x : U.polygon.Point) :
    (sum U V).label (sumPointEquiv U.polygon V.polygon (.inl x)).val.1=U.label x.val.1 := by
  simp [sumPointEquiv_inl]
@[simp] lemma sum_label_right (U V : Labelled a n) (x : V.polygon.Point) :
    (sum U V).label (sumPointEquiv U.polygon V.polygon (.inr x)).val.1=V.label x.val.1 := by
  simp [sumPointEquiv_inr]

noncomputable def sumHom {U V W Z : Labelled a n} (f : U ⟶ W) (g : V ⟶ Z) :
    sum U V ⟶ sum W Z where
  arrow := sumArrow f.arrow g.arrow
  positional := sumArrow_positional f.positional g.positional
  labelled x := by
    obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective x
    cases y with
    | inl y => simpa only [sumArrow_inl,sumPointEquiv_inl,Fin.addCases_left] using f.labelled y
    | inr y => simpa only [sumArrow_inr,sumPointEquiv_inr,Fin.addCases_right] using g.labelled y

noncomputable def assocHom (U V W : Labelled a n) : sum (sum U V) W ⟶ sum U (sum V W) where
  arrow := sumAssoc U.polygon V.polygon W.polygon
  positional := sumAssoc_positional _ _ _
  labelled x := by
    obtain ⟨y,rfl⟩ := (sumPointEquiv (sum U V).polygon W.polygon).surjective x
    cases y with
    | inl y =>
      obtain ⟨z,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective y
      cases z <;> simp only [sumAssoc_apply,sumAssocEquiv_left,sumAssocEquiv_mid,
        sumPointEquiv_inl,sumPointEquiv_inr] <;>
        simp only [PolygonObject.sum,Fin.addCases_left,Fin.addCases_right]
    | inr y =>
      simp only [sumAssoc_apply,sumAssocEquiv_right,sumPointEquiv_inr]
      simp only [PolygonObject.sum,Fin.addCases_right]

noncomputable def leftHom (U : Labelled a n) : sum empty U ⟶ U where
  arrow := leftUnit U.polygon
  positional := leftUnit_positional _
  labelled x := by
    obtain ⟨y,rfl⟩ := (sumPointEquiv PolygonObject.empty U.polygon).surjective x
    cases y with
    | inl y => exact isEmptyElim y
    | inr y =>
      simp only [leftUnit_apply,leftUnitEquiv_apply,sumPointEquiv_inr]
      simp only [PolygonObject.empty,Fin.addCases_right]

noncomputable def rightHom (U : Labelled a n) : sum U empty ⟶ U where
  arrow := rightUnit U.polygon
  positional := rightUnit_positional _
  labelled x := by
    obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon PolygonObject.empty).surjective x
    cases y with
    | inl y =>
      simp only [rightUnit_apply,rightUnitEquiv_apply,sumPointEquiv_inl]
      simp only [PolygonObject.empty,Fin.addCases_left]
    | inr y => exact isEmptyElim y

noncomputable def swapHom (U V : Labelled a n) : sum U V ⟶ sum V U where
  arrow := sumSwap U.polygon V.polygon
  positional := sumSwap_positional _ _
  labelled x := by
    obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective x
    cases y <;> simp only [sumSwap_apply,sumSwapEquiv_inl,sumSwapEquiv_inr,
      sumPointEquiv_inl,sumPointEquiv_inr,Fin.addCases_left,Fin.addCases_right]

instance : (forget (a:=a) (n:=n)).Faithful where
  map_injective h := Hom.ext _ _ h

noncomputable instance : MonoidalCategoryStruct (Labelled a n) where
  tensorObj := sum
  tensorHom := sumHom
  whiskerLeft U _ _ f := sumHom (𝟙 U) f
  whiskerRight f U := sumHom f (𝟙 U)
  tensorUnit := empty
  associator U V W := asIso (assocHom U V W)
  leftUnitor U := asIso (leftHom U)
  rightUnitor U := asIso (rightHom U)

noncomputable def inducing : Monoidal.InducingFunctorData (forget (a:=a) (n:=n)) where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  whiskerLeft_eq := by intros; simp only [Iso.refl_hom,Iso.refl_inv]; rfl
  whiskerRight_eq := by intros; simp only [Iso.refl_hom,Iso.refl_inv]; rfl
  tensorHom_eq := by intros; simp only [Iso.refl_hom,Iso.refl_inv]; rfl
  associator_eq := by
    intro U V W
    change sumAssoc U.polygon V.polygon W.polygon =
      (𝟙 _ ≫ sumArrow (𝟙 _) (𝟙 _)) ≫ sumAssoc U.polygon V.polygon W.polygon ≫
        (sumArrow (𝟙 _) (𝟙 _) ≫ 𝟙 _)
    simp only [sumArrow_id,Category.id_comp,Category.comp_id]
  leftUnitor_eq := by
    intro U
    change leftUnit U.polygon = (𝟙 _ ≫ sumArrow (𝟙 _) (𝟙 _)) ≫ leftUnit U.polygon
    rw [sumArrow_id,Category.id_comp,Category.id_comp]
  rightUnitor_eq := by
    intro U
    change rightUnit U.polygon = (𝟙 _ ≫ sumArrow (𝟙 _) (𝟙 _)) ≫ rightUnit U.polygon
    rw [sumArrow_id,Category.id_comp,Category.id_comp]

noncomputable instance : MonoidalCategory (Labelled a n) := Monoidal.induced forget inducing
noncomputable instance : (forget (a:=a) (n:=n)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal (Monoidal.fromInducedCoreMonoidal forget inducing)

noncomputable instance : BraidedCategory (Labelled a n) where
  braiding U V := asIso (swapHom U V)
  braiding_naturality_left := by
    intro U V f W
    apply forget.map_injective
    exact BraidedCategory.braiding_naturality_left f.arrow W.polygon
  braiding_naturality_right := by
    intro U V W f
    apply forget.map_injective
    exact BraidedCategory.braiding_naturality_right U.polygon f.arrow
  hexagon_forward := by
    intro U V W
    apply forget.map_injective
    exact BraidedCategory.hexagon_forward U.polygon V.polygon W.polygon
  hexagon_reverse := by
    intro U V W
    apply forget.map_injective
    change (inv (assocHom U V W)).arrow ≫ (swapHom (sum U V) W).arrow ≫
      (inv (assocHom W U V)).arrow =
      sumArrow (𝟙 U.polygon) (swapHom V W).arrow ≫ (inv (assocHom U W V)).arrow ≫
      sumArrow (swapHom U W).arrow (𝟙 V.polygon)
    simp only [inv_arrow]
    exact BraidedCategory.hexagon_reverse U.polygon V.polygon W.polygon

noncomputable instance : SymmetricCategory (Labelled a n) where
  symmetry U V := by
    apply forget.map_injective
    exact SymmetricCategory.symmetry U.polygon V.polygon

end Labelled
end SimpleAmenable.PolygonObject

end

end

end OAI
