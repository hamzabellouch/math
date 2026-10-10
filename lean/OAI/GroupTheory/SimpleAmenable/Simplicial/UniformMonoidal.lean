import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TrajectoryStages
import OAI.GroupTheory.SimpleAmenable.Simplicial.LabelledMonoidal

namespace OAI

section

section

open CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject

namespace Labelled
variable {a n : ℕ} (P : BooleanPartition a)

lemma objectUniform_sum {U V : Labelled a n} (hU : ObjectUniform P U) (hV : ObjectUniform P V) :
    ObjectUniform P (sum U V) := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i x y h; simpa only [PolygonObject.sum,Fin.addCases_left] using hU i x y h
  · intro i x y h; simpa only [PolygonObject.sum,Fin.addCases_right] using hV i x y h

lemma arrowUniform_sum {U V W Z : Labelled a n} {f : U ⟶ W} {g : V ⟶ Z}
    (hf : ArrowUniform P f) (hg : ArrowUniform P g) : ArrowUniform P (sumHom f g) := by
  intro x y h hP
  obtain ⟨x,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective x
  obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective y
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      simp only [sumPointEquiv_inl] at h
      have h := Fin.castAdd_inj.mp h
      simp only [sumHom,sumArrow_inl,sumPointEquiv_inl]
      simpa only [PolygonObject.sum] using
        congrArg (Fin.castAdd Z.polygon.tracks) (hf x y h hP)
    | inr y =>
      have he := congrArg Fin.val h
      simp only [sumPointEquiv_inl,sumPointEquiv_inr,Fin.val_castAdd,Fin.val_natAdd] at he
      have hx := x.val.1.isLt
      omega
  | inr x =>
    cases y with
    | inl y =>
      have he := congrArg Fin.val h
      simp only [sumPointEquiv_inl,sumPointEquiv_inr,Fin.val_castAdd,Fin.val_natAdd] at he
      have hy := y.val.1.isLt
      omega
    | inr y =>
      simp only [sumPointEquiv_inr] at h
      have h := (Fin.natAdd_inj _).mp h
      simp only [sumHom,sumArrow_inr,sumPointEquiv_inr]
      simpa only [PolygonObject.sum] using
        congrArg (Fin.natAdd W.polygon.tracks) (hg x y h hP)

lemma relabel_uniform {U V : PolygonObject a} (e : U.Point ≃ V.Point)
    (r : Fin U.tracks → Fin V.tracks)
    (he : ∀ x, (e x).val=(r x.val.1,x.val.2)) :
    ∀ x y, x.val.1=y.val.1 → P.color x.val.2=P.color y.val.2 →
      ((relabelArrow e r he).toEquiv x).val.1=((relabelArrow e r he).toEquiv y).val.1 := by
  intro x y h _
  change (e x).val.1=(e y).val.1
  rw [he x,he y,h]

lemma assocHom_uniform (U V W : Labelled a n) : ArrowUniform P (assocHom U V W) := by
  exact relabel_uniform P (sumAssocEquiv U.polygon V.polygon W.polygon)
    (Fin.addCases
      (Fin.addCases (fun i => i.castAdd (V.polygon.tracks+W.polygon.tracks)) (fun i => (i.castAdd W.polygon.tracks).natAdd U.polygon.tracks))
      (fun i => (i.natAdd V.polygon.tracks).natAdd U.polygon.tracks)) (by
      intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv (PolygonObject.sum U.polygon V.polygon) W.polygon).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective y
        cases z <;> simp only [sumAssocEquiv_left,sumAssocEquiv_mid,sumPointEquiv_inl,sumPointEquiv_inr] <;>
          simp only [PolygonObject.sum,Fin.addCases_left,Fin.addCases_right]
      | inr y =>
        simp only [sumAssocEquiv_right,sumPointEquiv_inr]
        simp only [PolygonObject.sum,Fin.addCases_right])
lemma swapHom_uniform (U V : Labelled a n) : ArrowUniform P (swapHom U V) := by
  exact relabel_uniform P (sumSwapEquiv U.polygon V.polygon)
    (Fin.addCases (fun i => i.natAdd V.polygon.tracks) (fun i => i.castAdd U.polygon.tracks)) (by
      intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective x
      cases y <;> simp only [sumSwapEquiv_inl,sumSwapEquiv_inr,sumPointEquiv_inl,sumPointEquiv_inr] <;>
        simp only [PolygonObject.sum,Fin.addCases_left,Fin.addCases_right])
lemma leftHom_uniform (U : Labelled a n) : ArrowUniform P (leftHom U) := by
  exact relabel_uniform P (leftUnitEquiv U.polygon) (Fin.addCases Fin.elim0 id) (by
    intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv PolygonObject.empty U.polygon).surjective x
    cases y with
    | inl y => exact isEmptyElim y
    | inr y =>
      simp only [leftUnitEquiv_apply,sumPointEquiv_inr]
      simp only [PolygonObject.empty,Fin.addCases_right,id_eq])
lemma rightHom_uniform (U : Labelled a n) : ArrowUniform P (rightHom U) := by
  exact relabel_uniform P (rightUnitEquiv U.polygon) (Fin.addCases id Fin.elim0) (by
    intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon PolygonObject.empty).surjective x
    cases y with
    | inl y =>
      simp only [rightUnitEquiv_apply,sumPointEquiv_inl]
      simp only [PolygonObject.empty,Fin.addCases_left,id_eq]
    | inr y => exact isEmptyElim y)

lemma sumHom_id (U V : Labelled a n) : sumHom (𝟙 U) (𝟙 V)=𝟙 (sum U V) :=
  Hom.ext _ _ (sumArrow_id _ _)
end Labelled

namespace LabelledStage.UniformObject
variable {a n s : ℕ} {P : BooleanPartition a} {L : Fin s → Fin n → CutRing × CutRing}

noncomputable abbrev sum (U V : UniformObject P L) : UniformObject P L where
  obj := Labelled.sum U.obj V.obj
  uniform := Labelled.objectUniform_sum P U.uniform V.uniform
  supported j := by
    refine Fin.addCases ?_ ?_ j
    · intro i; simpa only [Fin.addCases_left] using U.supported i
    · intro i; simpa only [Fin.addCases_right] using V.supported i

noncomputable abbrev empty : UniformObject P L where
  obj := Labelled.empty
  uniform j := Fin.elim0 j
  supported j := Fin.elim0 j

noncomputable def sumHom {U V W Z : UniformObject P L} (f : U ⟶ W) (g : V ⟶ Z) :
    sum U V ⟶ sum W Z :=
  ⟨Labelled.sumHom f.arrow g.arrow,Labelled.arrowUniform_sum P f.uniform g.uniform⟩
noncomputable def assocHom (U V W : UniformObject P L) : sum (sum U V) W ⟶ sum U (sum V W) :=
  ⟨Labelled.assocHom U.obj V.obj W.obj,Labelled.assocHom_uniform P _ _ _⟩
noncomputable def leftHom (U : UniformObject P L) : sum empty U ⟶ U :=
  ⟨Labelled.leftHom U.obj,Labelled.leftHom_uniform P _⟩
noncomputable def rightHom (U : UniformObject P L) : sum U empty ⟶ U :=
  ⟨Labelled.rightHom U.obj,Labelled.rightHom_uniform P _⟩
noncomputable def swapHom (U V : UniformObject P L) : sum U V ⟶ sum V U :=
  ⟨Labelled.swapHom U.obj V.obj,Labelled.swapHom_uniform P _ _⟩

noncomputable instance : MonoidalCategoryStruct (UniformObject P L) where
  tensorObj := sum
  tensorHom := sumHom
  whiskerLeft U _ _ f := sumHom (𝟙 U) f
  whiskerRight f U := sumHom f (𝟙 U)
  tensorUnit := empty
  associator U V W := asIso (assocHom U V W)
  leftUnitor U := asIso (leftHom U)
  rightUnitor U := asIso (rightHom U)

noncomputable def inducing : Monoidal.InducingFunctorData (forget (P:=P) (L:=L)) where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  whiskerLeft_eq := by intros; simp only [Iso.refl_hom,Iso.refl_inv]; rfl
  whiskerRight_eq := by intros; simp only [Iso.refl_hom,Iso.refl_inv]; rfl
  tensorHom_eq := by intros; simp only [Iso.refl_hom,Iso.refl_inv]; rfl
  associator_eq := by
    intro U V W
    change Labelled.assocHom U.obj V.obj W.obj =
      (𝟙 _ ≫ Labelled.sumHom (𝟙 _) (𝟙 _)) ≫ Labelled.assocHom U.obj V.obj W.obj ≫
        (Labelled.sumHom (𝟙 _) (𝟙 _) ≫ 𝟙 _)
    simp only [Labelled.sumHom_id,Category.id_comp,Category.comp_id]
  leftUnitor_eq := by
    intro U
    change Labelled.leftHom U.obj = (𝟙 _ ≫ Labelled.sumHom (𝟙 _) (𝟙 _)) ≫ Labelled.leftHom U.obj
    rw [Labelled.sumHom_id,Category.id_comp,Category.id_comp]
  rightUnitor_eq := by
    intro U
    change Labelled.rightHom U.obj = (𝟙 _ ≫ Labelled.sumHom (𝟙 _) (𝟙 _)) ≫ Labelled.rightHom U.obj
    rw [Labelled.sumHom_id,Category.id_comp,Category.id_comp]

noncomputable instance : MonoidalCategory (UniformObject P L) := Monoidal.induced forget inducing
noncomputable instance : (forget (P:=P) (L:=L)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal (Monoidal.fromInducedCoreMonoidal forget inducing)

noncomputable instance : BraidedCategory (UniformObject P L) :=
  BraidedCategory.ofFaithful forget (fun U V => asIso (swapHom U V)) (by
    intro U V
    change (𝟙 _) ≫ Labelled.swapHom U.obj V.obj = Labelled.swapHom U.obj V.obj ≫ (𝟙 _)
    simp)
noncomputable instance : (forget (P:=P) (L:=L)).Braided where
  braided U V := by
    change (𝟙 _) ≫ Labelled.swapHom U.obj V.obj = Labelled.swapHom U.obj V.obj ≫ (𝟙 _)
    simp
noncomputable instance : SymmetricCategory (UniformObject P L) := SymmetricCategory.ofFaithful forget

end LabelledStage.UniformObject
end SimpleAmenable.PolygonObject

end

end

end OAI
