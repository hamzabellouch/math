import OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws
import OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingTransitions

namespace OAI

noncomputable section

namespace PiExponentSeshadri.LineBundleGluing
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

def Cocycle.one : Cocycle U where
  transition _ _ _ _ _ := 1
  restriction _ _ _ _ _ := by simp
  identity _ _ _ := rfl
  cocycle _ _ _ _ _ _ _ := one_mul _

def Cocycle.inverse (c : Cocycle U) : Cocycle U where
  transition i j W hi hj := (c.transition i j W hi hj)⁻¹
  restriction := by
    intro i j V W h hi hj
    have h' : restrictUnit h (c.transition i j _ hi hj) =
        c.transition i j _ (h.trans hi) (h.trans hj) := Units.ext (c.restriction i j h hi hj)
    exact congrArg Units.val ((map_inv (restrictUnit h) _).symm.trans (congrArg Inv.inv h'))
  identity i W hi := by rw [c.identity, inv_one]
  cocycle i j k W hi hj hk := by rw [← mul_inv, c.cocycle]

def inverseProduct (c : Cocycle U) (V : X.Opens)
    (s : sections c V) (t : sections c.inverse V) : sections (Cocycle.one (U := U)) V :=
  ⟨fun p => s.val p * t.val p, by
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op (_ * _) = _
      rw [map_mul, s.property.1 i W W' hW hi h, t.property.1 i W W' hW hi h]
    · intro i j W hW hi hj
      change s.val ⟨i,W,hW,hi⟩ * t.val ⟨i,W,hW,hi⟩ = 1 * _
      rw [s.property.2 i j W hW hi hj, t.property.2 i j W hW hi hj, one_mul]
      change (_ * _) * ((↑((c.transition i j W hi hj)⁻¹ : Γ(X,W)ˣ) : Γ(X,W)) * _) = _
      rw [mul_mul_mul_comm, Units.mul_inv, one_mul]⟩

def inverseProductMap (c : Cocycle U) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
      (presheaf c) (presheaf c.inverse) ⟶ presheaf (Cocycle.one (U := U)) where
  app V := ModuleCat.MonoidalCategory.tensorLift (inverseProduct c V.unop)
    (by intros; apply Subtype.ext; funext p; exact add_mul _ _ _)
    (by intros; apply Subtype.ext; funext p; exact mul_assoc _ _ _)
    (by intros; apply Subtype.ext; funext p; exact mul_add _ _ _)
    (by intros; apply Subtype.ext; funext p; exact mul_left_comm _ _ _)
  naturality {V W} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    rfl

def trivialCoefficientMap : (structureSheaf X).val ⟶ presheaf (Cocycle.one (U := U)) where
  app V := ModuleCat.ofHom (R := Γ(X, V.unop))
    (X := ModuleCat.of Γ(X, V.unop) Γ(X, V.unop))
    (Y := ModuleCat.of Γ(X, V.unop) (sections (Cocycle.one (U := U)) V.unop)) {
    toFun a := ⟨fun p => X.presheaf.map (homOfLE p.2.property.1).op a, by
      constructor
      · intro i W W' hW hi h
        change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
        rw [← Functor.map_comp]
        rfl
      · intros; exact (one_mul _).symm⟩
    map_add' a b := by apply Subtype.ext; funext p; exact map_add _ _ _
    map_smul' a b := by apply Subtype.ext; funext p; exact map_mul _ _ _ }
  naturality {V W} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext p
    change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
    rw [← Functor.map_comp]
    rfl

lemma cocycleUnit_restrict_isIso (c : Cocycle U) (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map ((adj X).unit.app (presheaf c))) := by
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules (U i).toScheme.ringCatSheaf.obj := modulePresheafRestrict (U i).ι
  have hη : IsIso ((adj (U i).toScheme).unit.app (R.obj (presheaf c))) :=
    sheafification_unit_isIso_of_iso _ (structureSheaf (U i).toScheme)
      (chartPresheafFrame c i)
  have hh : IsIso (R.map ((adj X).unit.app (presheaf c)) ≫
      ((moduleSheafificationRestrict (U i).ι).hom.app (presheaf c)).val) := by
    erw [sheafify_restrict_unit]
    exact hη
  let V : (U i).toScheme.Modules ⥤ PresheafOfModules (U i).toScheme.ringCatSheaf.obj :=
    SheafOfModules.forget (U i).toScheme.ringCatSheaf
  let hv : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      (((moduleSheafificationRestrict (U i).ι).hom.app (presheaf c)).val) :=
    (V.mapIso ((moduleSheafificationRestrict (U i).ι).app (presheaf c))).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hv).mp hh

lemma trivialCoefficientMap_frame (i : ι) :
    (modulePresheafRestrict (U i).ι).map (trivialCoefficientMap (U := U)) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom =
    (Scheme.Modules.restrictUnitIso (U i).ι).hom.val := by
  ext V a
  change X.presheaf.map (homOfLE (show (U i).ι ''ᵁ V.unop ≤ (U i).ι ''ᵁ V.unop from le_rfl)).op a = _
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
  change a = ((U i).ι.appIso V.unop).hom a
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom]
  rfl

lemma trivialCoefficientMap_restrict_isIso (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map (trivialCoefficientMap (U := U))) := by
  let V : (U i).toScheme.Modules ⥤ PresheafOfModules (U i).toScheme.ringCatSheaf.obj :=
    SheafOfModules.forget (U i).toScheme.ringCatSheaf
  have hv : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      ((Scheme.Modules.restrictUnitIso (U i).ι).hom.val) :=
    (V.mapIso (Scheme.Modules.restrictUnitIso (U i).ι)).isIso_hom
  have hh : IsIso ((modulePresheafRestrict (U i).ι).map (trivialCoefficientMap (U := U)) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom) := by
    rw [trivialCoefficientMap_frame]
    exact hv
  let hc : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom :=
    (chartPresheafFrame (Cocycle.one (U := U)) i).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hc).mp hh

lemma inverseProductMap_frame (c : Cocycle U) (i : ι) :
    (modulePresheafRestrict (U i).ι).map (inverseProductMap c) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom =
    (modulePresheafTensorRestrict (U i) (presheaf c) (presheaf c.inverse)).hom ≫
      PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := (U i).toScheme.presheaf)
        (chartPresheafFrame c i).hom (chartPresheafFrame c.inverse i).hom ≫
      (by
        let : MonoidalCategory (PresheafOfModules (U i).toScheme.ringCatSheaf.obj) :=
          PresheafOfModulesOfCommRing.monoidalCategory (R := (U i).toScheme.presheaf)
        exact (λ_ (structureSheaf (U i).toScheme).val).hom) := by
  let : MonoidalCategory (PresheafOfModules (U i).toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := (U i).toScheme.presheaf)
  let l := (modulePresheafRestrict (U i).ι).map (inverseProductMap c) ≫
    (chartPresheafFrame (Cocycle.one (U := U)) i).hom
  let r := (modulePresheafTensorRestrict (U i) (presheaf c) (presheaf c.inverse)).hom ≫
    PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := (U i).toScheme.presheaf)
      (chartPresheafFrame c i).hom (chartPresheafFrame c.inverse i).hom ≫
    (λ_ (structureSheaf (U i).toScheme).val).hom
  change l = r
  ext V : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s t => rfl
  | add a b ha hb =>
      exact ((l.app V).hom.map_add a b).trans
        ((congrArg₂ (· + ·) ha hb).trans ((r.app V).hom.map_add a b).symm)

lemma inverseProductMap_restrict_isIso (c : Cocycle U) (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map (inverseProductMap c)) := by
  let : MonoidalCategory (PresheafOfModules (U i).toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := (U i).toScheme.presheaf)
  let e := modulePresheafTensorRestrict (U i) (presheaf c) (presheaf c.inverse) ≪≫
    tensorIso (chartPresheafFrame c i) (chartPresheafFrame c.inverse i) ≪≫
      λ_ (structureSheaf (U i).toScheme).val
  have hh : IsIso ((modulePresheafRestrict (U i).ι).map (inverseProductMap c) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom) := by
    rw [inverseProductMap_frame]
    exact e.isIso_hom
  let hc : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom :=
    (chartPresheafFrame (Cocycle.one (U := U)) i).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hc).mp hh

lemma sheafification_isIso_of_chart {P Q : PresheafOfModules X.ringCatSheaf.obj}
    (f : P ⟶ Q) (hcover : ⊤ ≤ ⨆ i, U i)
    (hf : ∀ i, IsIso ((modulePresheafRestrict (U i).ι).map f)) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f) := by
  apply PiExponent.NumericalAmpleness.isIso_of_locally_isIso
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover (show x ∈ (⊤ : X.Opens) from trivial))
  refine ⟨U i, hi, ?_⟩
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict (U i).ι) f).mpr
  have := hf i
  change IsIso ((PresheafOfModules.sheafification (𝟙 (U i).toScheme.ringCatSheaf.obj)).map
    ((modulePresheafRestrict (U i).ι).map f))
  infer_instance

end PiExponentSeshadri.LineBundleGluing

end

end OAI
