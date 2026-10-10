import OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections

namespace OAI

namespace PiExponent.GeometrySupport.PushforwardOpenSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.ProjectiveChartSections
open CechOne CechHigher

private abbrev schemeFreeOpen (X : Scheme.{0}) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X Y : Scheme.{0}} (f : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (β : M ⟶ (Scheme.Modules.pushforward f).obj N)

def sectionMap (U : X.Opens) :
    (schemeFreeOpen X U ⟶ M) →+
      (schemeFreeOpen Y (f ⁻¹ᵁ U) ⟶ N) where
  toFun b := (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm
    (β.app U (freeOpenAddEquiv U M b))
  map_zero' := by
    change (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm
      ((β.app U).hom (freeOpenAddEquiv U M 0)) = 0
    rw [_root_.map_zero, _root_.map_zero]
    exact (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm.map_zero
  map_add' b c := by
    change (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm
      ((β.app U).hom (freeOpenAddEquiv U M (b + c))) = _
    rw [_root_.map_add, _root_.map_add]
    exact (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm.map_add _ _

@[simp] theorem sectionMap_value (U : X.Opens) (b : schemeFreeOpen X U ⟶ M) :
    freeOpenAddEquiv (f ⁻¹ᵁ U) N (sectionMap f β U b) =
      β.app U (freeOpenAddEquiv U M b) := AddEquiv.apply_symm_apply _ _

theorem sectionMap_bijective (U : X.Opens) (h : Function.Bijective (β.app U)) :
    Function.Bijective (sectionMap f β U) :=
  (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm.bijective.comp
    (h.comp (freeOpenAddEquiv U M).bijective)

theorem sectionMap_injective (U : X.Opens) (h : Function.Injective (β.app U)) :
    Function.Injective (sectionMap f β U) :=
  (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm.injective.comp
    (h.comp (freeOpenAddEquiv U M).injective)

theorem sectionMap_restrict {U V : X.Opens} (h : U ≤ V)
    (b : schemeFreeOpen X V ⟶ M) :
    sectionMap f β U (restrictHom X.ringCatSheaf h b) =
      restrictHom Y.ringCatSheaf (f.preimage_mono h) (sectionMap f β V b) := by
  apply (freeOpenAddEquiv (f ⁻¹ᵁ U) N).injective
  erw [sectionMap_value]
  change β.app U (freeOpenEquiv X.ringCatSheaf M U
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b)) =
    freeOpenEquiv Y.ringCatSheaf N (f ⁻¹ᵁ U)
      (freeOpenMap Y.ringCatSheaf (homOfLE (f.preimage_mono h)) ≫ sectionMap f β V b)
  have hleft := freeOpenEquiv_naturality X.ringCatSheaf M (homOfLE h) b
  have hright := freeOpenEquiv_naturality Y.ringCatSheaf N
    (homOfLE (f.preimage_mono h)) (sectionMap f β V b)
  have hn := PresheafOfModules.naturality_apply β.val (homOfLE h).op
    (freeOpenEquiv X.ringCatSheaf M V b)
  change β.app U (M.presheaf.map (homOfLE h).op _) =
    N.presheaf.map (homOfLE (f.preimage_mono h)).op
      (β.app V (freeOpenAddEquiv V M b)) at hn
  exact (congrArg (β.app U) hleft).trans
    (hn.trans ((congrArg (N.presheaf.map (homOfLE (f.preimage_mono h)).op)
      (sectionMap_value f β V b).symm).trans hright.symm))

def restrictEquiv (N : Y.Modules) {U V : Y.Opens} (h : U ≤ V) (h' : V ≤ U) :
    (schemeFreeOpen Y V ⟶ N) ≃+ (schemeFreeOpen Y U ⟶ N) where
  toFun := restrictHom Y.ringCatSheaf h
  invFun := restrictHom Y.ringCatSheaf h'
  left_inv b := by erw [restrictHom_restrictHom, restrictHom_refl]
  right_inv b := by erw [restrictHom_restrictHom, restrictHom_refl]
  map_add' := restrictHom_add Y.ringCatSheaf h

end
end PiExponent.GeometrySupport.PushforwardOpenSections

end OAI
