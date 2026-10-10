import OAI.NumberTheory.PiExponent.Approximation.CocycleTensor

namespace OAI

namespace PiExponentSeshadri.LineBundleGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

lemma tensorHom_restrict_isIso (W : X.Opens)
    {P P' Q Q' : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ P') (g : Q ⟶ Q')
    [IsIso ((modulePresheafRestrict W.ι).map f)]
    [IsIso ((modulePresheafRestrict W.ι).map g)] :
    IsIso ((modulePresheafRestrict W.ι).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f g)) := by
  let R := modulePresheafRestrict W.ι
  let : MonoidalCategory (PresheafOfModules W.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := W.toScheme.presheaf)
  have hh : IsIso (R.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f g) ≫
      (modulePresheafTensorRestrict W P' Q').hom) := by
    rw [modulePresheafTensorRestrict_natural]
    change IsIso (_ ≫ (R.map f ⊗ₘ R.map g))
    infer_instance
  let hc : IsIso (C := PresheafOfModules W.toScheme.ringCatSheaf.obj)
      (modulePresheafTensorRestrict W P' Q').hom :=
    (modulePresheafTensorRestrict W P' Q').isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules W.toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hc).mp hh

def cocycleTensorComparison (c d : Cocycle U) (hcover : ⊤ ≤ ⨆ i, U i) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
        (presheaf c) (presheaf d)) ≅ moduleTensor X (sheaf c) (sheaf d) := by
  let f := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    ((adj X).unit.app (presheaf c)) ((adj X).unit.app (presheaf d))
  have ht : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f) := by
    apply sheafification_isIso_of_chart f hcover
    intro i
    have := cocycleUnit_restrict_isIso c i
    have := cocycleUnit_restrict_isIso d i
    exact tensorHom_restrict_isIso (U i) _ _
  exact @asIso _ _ _ _ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f) ht

def trivialSheafIso (hcover : ⊤ ≤ ⨆ i, U i) :
    sheaf (Cocycle.one (U := U)) ≅ structureSheaf X := by
  have ht : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (trivialCoefficientMap (U := U))) :=
    sheafification_isIso_of_chart _ hcover trivialCoefficientMap_restrict_isIso
  exact (@asIso _ _ _ _ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (trivialCoefficientMap (U := U))) ht).symm ≪≫
      (asIso (adj X).counit).app (structureSheaf X)

def tensorInverseIso (c : Cocycle U) (hcover : ⊤ ≤ ⨆ i, U i) :
    moduleTensor X (sheaf c) (sheaf c.inverse) ≅ structureSheaf X := by
  have ht : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (inverseProductMap c)) :=
    sheafification_isIso_of_chart _ hcover (inverseProductMap_restrict_isIso c)
  exact (cocycleTensorComparison c c.inverse hcover).symm ≪≫
    @asIso _ _ _ _ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (inverseProductMap c)) ht ≪≫
      trivialSheafIso hcover

end
end PiExponentSeshadri.LineBundleGluing

end OAI
