import OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws
import OAI.NumberTheory.PiExponent.Approximation.TensorPure
import OAI.NumberTheory.PiExponent.Geometry.SheafificationUnitIso

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open PiExponentSeshadri.TensorPure
variable {X : Scheme}

def lineTensorPresheafRestrictFrame (L : LineBundle X) (N : X.Modules)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    (modulePresheafRestrict U.ι).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val) ≅
        (N.restrict U.ι).val := by
  let : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := U.toScheme.presheaf)
  let ep : (modulePresheafRestrict U.ι).obj L.sheaf.val ≅
      𝟙_ (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    (SheafOfModules.forget _).mapIso e
  exact modulePresheafTensorRestrict U L.sheaf.val N.val ≪≫
    tensorIso ep (Iso.refl _) ≪≫ λ_ _

lemma lineTensorPresheaf_unit_restrict_isIso (L : LineBundle X) (N : X.Modules)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    IsIso ((modulePresheafRestrict U.ι).map
      ((adj X).unit.app
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val))) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  have hη : IsIso ((adj U.toScheme).unit.app (R.obj P)) :=
    sheafification_unit_isIso_of_iso (R.obj P) (N.restrict U.ι)
      (lineTensorPresheafRestrictFrame L N U e)
  have hh : IsIso (R.map ((adj X).unit.app P) ≫
      ((moduleSheafificationRestrict U.ι).hom.app P).val) := by
    erw [sheafify_restrict_unit]
    exact hη
  let V : U.toScheme.Modules ⥤ PresheafOfModules U.toScheme.ringCatSheaf.obj :=
    SheafOfModules.forget U.toScheme.ringCatSheaf
  let hv : IsIso (C := PresheafOfModules U.toScheme.ringCatSheaf.obj)
      (((moduleSheafificationRestrict U.ι).hom.app P).val) :=
    (V.mapIso ((moduleSheafificationRestrict U.ι).app P)).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules U.toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hv).mp hh

lemma sheafification_tensor_left_line_unit_isIso (M : X.Modules) (L : LineBundle X)
    (N : X.Modules) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) (𝟙 M.val)
        ((adj X).unit.app
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val)))) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (adj X).unit.app P
  let Q := (F ⋙ SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P
  let g := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) (𝟙 M.val) η
  apply PiExponent.NumericalAmpleness.isIso_of_locally_isIso
  intro x
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U,hx,?_⟩
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  let S : PresheafOfModules U.toScheme.ringCatSheaf.obj ⥤ U.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)
  let : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := U.toScheme.presheaf)
  have : IsIso (R.map η) := lineTensorPresheaf_unit_restrict_isIso L N U e
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) g).mpr
  change IsIso (S.map (R.map g))
  have heq := modulePresheafTensorRestrict_natural U (𝟙 M.val) η
  let : IsIso (S.map (modulePresheafTensorRestrict U M.val P).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U M.val P)).isIso_hom
  let : IsIso (S.map (modulePresheafTensorRestrict U M.val Q).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U M.val Q)).isIso_hom
  have hcomp : IsIso (S.map (R.map g ≫
      (modulePresheafTensorRestrict U M.val Q).hom)) := by
    erw [heq, S.map_comp]
    have ht : IsIso (S.map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
        (R.map (𝟙 M.val)) (R.map η))) := by
      rw [R.map_id]
      change IsIso (S.map ((𝟙 (R.obj M.val)) ⊗ₘ (R.map η)))
      infer_instance
    exact (inferInstance : IsIso (C := U.toScheme.Modules)
      (S.map (modulePresheafTensorRestrict U M.val P).hom ≫ S.map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
          (R.map (𝟙 M.val)) (R.map η))))
  erw [S.map_comp] at hcomp
  exact (isIso_comp_right_iff (C := U.toScheme.Modules) _ _).mp hcomp

def sheafificationTensorLeftLinePair (M : X.Modules) (L N : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.sheaf.val)) ≅
    moduleTensor X M (moduleTensor X L.sheaf N.sheaf) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.sheaf.val
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (adj X).unit.app P
  let ht : IsIso (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom
      (R := X.presheaf) (𝟙 M.val) η)) := sheafification_tensor_left_line_unit_isIso M L N.sheaf
  exact @asIso _ _ _ _ (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    (𝟙 M.val) η)) ht

def moduleLineTensorAssoc (M : X.Modules) (L N : LineBundle X) :
    moduleTensor X (moduleTensor X M L.sheaf) N.sheaf ≅
      moduleTensor X M (moduleTensor X L.sheaf N.sheaf) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (sheafificationTensorRight (M.val ⊗ L.sheaf.val) N).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (α_ M.val L.sheaf.val N.sheaf.val) ≪≫
    sheafificationTensorLeftLinePair M L N

def moduleTwistPowerIso (L : LineBundle X) (M : X.Modules) : ∀ n : ℕ,
    (moduleTwistFunctor L n).obj M ≅ moduleTensor X M (modulePow X L.sheaf n)
  | 0 => (moduleTensorRightUnit M).symm
  | n+1 => moduleTensorIso (moduleTwistPowerIso L M n) (Iso.refl L.sheaf) ≪≫
      moduleLineTensorAssoc M (L.pow n) L ≪≫
      moduleTensorIso (Iso.refl M) (moduleTensorComm (modulePow X L.sheaf n) L.sheaf)

def moduleTwistPowerMulIso (L : LineBundle X) (M : X.Modules) (d n : ℕ) :
    (moduleTwistFunctor (L.pow d) n).obj M ≅ (moduleTwistFunctor L (d*n)).obj M :=
  moduleTwistPowerIso (L.pow d) M n ≪≫
    moduleTensorIso (Iso.refl M) (linePowerMul L d n) ≪≫
      (moduleTwistPowerIso L M (d*n)).symm

end
end PiExponentSeshadri.Geometry

end OAI
