import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.LabelledMonoidal

namespace OAI

open CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled

variable {a n : ℕ} (d : (Fin n → CutRing × CutRing) → CutRing × CutRing)
noncomputable def translateObj (U : Labelled a n) : Labelled a n where
  polygon := shifted U.polygon (fun i => d (U.label i))
  label := U.label
  reduced := U.reduced
noncomputable abbrev translateArrow (U : Labelled a n) : U.polygon ⟶ (translateObj d U).polygon :=
  shiftArrow U.polygon (fun i => d (U.label i))
noncomputable def translateHom {U V : Labelled a n} (f : U ⟶ V) : translateObj d U ⟶ translateObj d V where
  arrow := inv (translateArrow d U) ≫ f.arrow ≫ translateArrow d V
  positional x := by
    obtain ⟨y,rfl⟩ := (translateArrow d U).toEquiv.surjective x
    simp only [arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
    change translate a (d (V.label (f.arrow.toEquiv y).val.1)) (f.arrow.toEquiv y).val.2 =
      translate a (d (U.label y.val.1)) y.val.2
    rw [f.labelled,f.positional]
  labelled x := by
    obtain ⟨y,rfl⟩ := (translateArrow d U).toEquiv.surjective x
    simp only [arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
    exact f.labelled y
noncomputable def translateFunctor : Labelled a n ⥤ Labelled a n where
  obj := translateObj d
  map := translateHom d
  map_id U := by
    apply Hom.ext
    change inv _ ≫ 𝟙 _ ≫ _ = _
    simp
    rfl
  map_comp f g := by
    apply Hom.ext
    change inv _ ≫ (f.arrow ≫ g.arrow) ≫ _ = (inv _ ≫ f.arrow ≫ _) ≫ (inv _ ≫ g.arrow ≫ _)
    simp only [Category.assoc,IsIso.hom_inv_id_assoc]
noncomputable def translationIso : forget (a:=a) (n:=n) ≅ translateFunctor d ⋙ forget :=
  NatIso.ofComponents (fun U => by
    let e := asIso (translateArrow d U)
    exact e) (by
    intro U V f
    change f.arrow ≫ translateArrow d V = translateArrow d U ≫
      (inv (translateArrow d U) ≫ f.arrow ≫ translateArrow d V)
    simp)
noncomputable def translationCore : (translateFunctor (a:=a) d ⋙ forget).CoreMonoidal :=
  Functor.Monoidal.coreMonoidalTransport (translationIso d)
lemma translationCore_unit : (translationCore (a:=a) d).εIso.hom=translateArrow d (𝟙_ _) := by
  exact Category.id_comp (translateArrow d (𝟙_ _))
lemma translationCore_tensor (U V:Labelled a n) :
    ((translationCore d).μIso U V).hom =
      inv (sumArrow (translateArrow d U) (translateArrow d V)) ≫ translateArrow d (U⊗V) := by
  change (inv (translateArrow d U) ⊗ₘ inv (translateArrow d V)) ≫ 𝟙 _ ≫ _ = _
  erw [Category.id_comp]
  congr 1
  apply (cancel_epi (sumArrow (translateArrow d U) (translateArrow d V))).mp
  change (_ ⊗ₘ _) ≫ (_ ⊗ₘ _) = _
  rw [tensorHom_comp_tensorHom]
  simp
  rfl
noncomputable def translationUnit : 𝟙_ (Labelled a n) ⟶ (translateFunctor d).obj (𝟙_ _) where
  arrow := translateArrow d (𝟙_ _)
  positional x := by change Point PolygonObject.empty at x; exact isEmptyElim x
  labelled x := by change Point PolygonObject.empty at x; exact isEmptyElim x
noncomputable def translationTensor (U V:Labelled a n) :
    (translateFunctor d).obj U ⊗ (translateFunctor d).obj V ⟶ (translateFunctor d).obj (U⊗V) where
  arrow := inv (sumArrow (translateArrow d U) (translateArrow d V)) ≫ translateArrow d (U⊗V)
  positional x := by
    erw [arrow_comp_apply,inv_arrow_apply]
    change ((translateArrow d (sum U V)).toEquiv
      ((sumArrow (translateArrow d U) (translateArrow d V)).toEquiv.symm x)).val.2 = x.val.2
    obtain ⟨y,rfl⟩ := (sumArrow (translateArrow d U) (translateArrow d V)).toEquiv.surjective x
    rw [Equiv.symm_apply_apply]
    change translate a (d ((sum U V).label y.val.1)) y.val.2 =
      ((sumArrow (translateArrow d U) (translateArrow d V)).toEquiv y).val.2
    obtain ⟨z,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective y
    cases z <;> (first | erw [sumArrow_inl] | erw [sumArrow_inr]) <;>
      simp only [sumPointEquiv_inl,sumPointEquiv_inr,
      translateArrow,Fin.addCases_left,Fin.addCases_right]
    all_goals rfl
  labelled x := by
    erw [arrow_comp_apply,inv_arrow_apply]
    change (sum U V).label ((translateArrow d (sum U V)).toEquiv
      ((sumArrow (translateArrow d U) (translateArrow d V)).toEquiv.symm x)).val.1 =
      (sum (translateObj d U) (translateObj d V)).label x.val.1
    obtain ⟨y,rfl⟩ := (sumArrow (translateArrow d U) (translateArrow d V)).toEquiv.surjective x
    rw [Equiv.symm_apply_apply]
    change (sum U V).label y.val.1 =
      (sum (translateObj d U) (translateObj d V)).label
        ((sumArrow (translateArrow d U) (translateArrow d V)).toEquiv y).val.1
    obtain ⟨z,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective y
    cases z <;> (first | erw [sumArrow_inl] | erw [sumArrow_inr]) <;> rfl
lemma translationTensor_arrow (U V : Labelled a n) :
    (translationTensor d U V).arrow=((translationCore d).μIso U V).hom := by
  rw [translationCore_tensor]; rfl
lemma translationUnit_arrow : (translationUnit (a:=a) d).arrow=(translationCore d).εIso.hom := by
  rw [translationCore_unit]; rfl
noncomputable instance translationMonoidal : (translateFunctor (a:=a) d).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := asIso (translationUnit d)
    μIso U V := asIso (translationTensor d U V)
    μIso_hom_natural_left := by
      intro U V f W
      apply Hom.ext
      change sumArrow (translateHom d f).arrow (𝟙 _) ≫ (translationTensor d V W).arrow =
        (translationTensor d U W).arrow ≫ (translateHom d (f ▷ W)).arrow
      rw [translationTensor_arrow,translationTensor_arrow]
      exact (translationCore d).μIso_hom_natural_left f W
    μIso_hom_natural_right := by
      intro U V W f
      apply Hom.ext
      change sumArrow (𝟙 _) (translateHom d f).arrow ≫ (translationTensor d W V).arrow =
        (translationTensor d W U).arrow ≫ (translateHom d (W ◁ f)).arrow
      rw [translationTensor_arrow,translationTensor_arrow]
      exact (translationCore d).μIso_hom_natural_right W f
    associativity := by
      intro U V W
      apply Hom.ext
      change sumArrow (translationTensor d U V).arrow (𝟙 _) ≫
        (translationTensor d (U⊗V) W).arrow ≫ (translateHom d (α_ U V W).hom).arrow =
        sumAssoc _ _ _ ≫ sumArrow (𝟙 _) (translationTensor d V W).arrow ≫
          (translationTensor d U (V⊗W)).arrow
      simp only [translationTensor_arrow]
      exact (translationCore d).associativity U V W
    left_unitality := by
      intro U
      apply Hom.ext
      change leftUnit _ = sumArrow (translationUnit d).arrow (𝟙 _) ≫
        (translationTensor d (𝟙_ _) U).arrow ≫ (translateHom d (λ_ U).hom).arrow
      rw [translationUnit_arrow,translationTensor_arrow]
      exact (translationCore d).left_unitality U
    right_unitality := by
      intro U
      apply Hom.ext
      change rightUnit _ = sumArrow (𝟙 _) (translationUnit d).arrow ≫
        (translationTensor d U (𝟙_ _)).arrow ≫ (translateHom d (ρ_ U).hom).arrow
      rw [translationUnit_arrow,translationTensor_arrow]
      exact (translationCore d).right_unitality U }
noncomputable instance translationBraided : (translateFunctor (a:=a) d).Braided where
  braided U V := by
    apply Hom.ext
    change (translationTensor d U V).arrow ≫ (translateHom d (β_ U V).hom).arrow =
      sumSwap _ _ ≫ (translationTensor d V U).arrow
    change (inv (sumArrow (translateArrow d U) (translateArrow d V)) ≫ translateArrow d (U⊗V)) ≫
      (inv (translateArrow d (U⊗V)) ≫ sumSwap _ _ ≫ translateArrow d (V⊗U)) =
      sumSwap _ _ ≫ inv (sumArrow (translateArrow d V) (translateArrow d U)) ≫ translateArrow d (V⊗U)
    simp only [Category.assoc,IsIso.hom_inv_id_assoc]
    apply (cancel_epi (sumArrow (translateArrow d U) (translateArrow d V))).mp
    simp only [IsIso.hom_inv_id_assoc]
    have h := BraidedCategory.braiding_naturality (translateArrow d U) (translateArrow d V)
    change sumArrow (translateArrow d U) (translateArrow d V) ≫ sumSwap _ _ =
      sumSwap _ _ ≫ sumArrow (translateArrow d V) (translateArrow d U) at h
    rw [←Category.assoc (sumArrow (translateArrow d U) (translateArrow d V)),h]
    simp
end SimpleAmenable.PolygonObject.Labelled

end OAI
