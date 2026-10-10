import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.SectionPullback
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PushforwardTensor

namespace OAI


                                        
section

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MonoidalCategory
open MaximalSeshadri.Frames MaximalSeshadri.Geometry

variable {X Y : Scheme.{0}}

attribute [local instance] sectionModule

lemma unit_pure (M : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) :
    (moduleTensorUnit M).hom.app U (pure (O X) M U a m) = a • m := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  have h := ((adj X).homEquiv _ _).apply_symm_apply (λ_ M.val).hom
  change (adj X).homEquiv _ M (moduleTensorUnit M).hom = (λ_ M.val).hom at h
  exact congrArg (fun q => q.app (op U) (a ⊗ₜ[Γ(X,U)] m)) h

end
end MaximalSeshadri.TensorPure

namespace MaximalSeshadri.PullbackTensor
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MonoidalCategory
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.TensorPure

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

lemma unit_compatibility :
    hom f (O Y) (O Y) ≫
      (moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom =
    (Scheme.Modules.pullback f).map (moduleTensorUnit (O Y)).hom ≫
      (pullbackUnitIso f).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  erw [(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left
    (moduleTensorUnit (O Y)).hom (pullbackUnitIso f).hom]
  rw [pullbackUnit_adjunction]
  simp only [hom, Equiv.apply_symm_apply]
  apply TensorPure.hom_ext
  intro U a b
  change (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U)
      ((PushforwardTensor.hom f _ _).app U ((moduleTensorMap _ _).app U
        (pure (O Y) (O Y) U a b)))) =
    (f.app U) ((moduleTensorUnit (O Y)).hom.app U (pure (O Y) (O Y) U a b))
  rw [map_pure]
  refine (congrArg (fun sectionValue =>
    (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
      ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U)
        sectionValue))
    (PushforwardTensor.hom_pure f _ _ U _ _)).trans ?_
  refine (congrArg ((moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U))
    (map_pure (pullbackUnitIso f).hom (pullbackUnitIso f).hom (f ⁻¹ᵁ U) _ _)).trans ?_
  refine (unit_pure (O X) (f ⁻¹ᵁ U) _ _).trans ?_
  refine Eq.trans ?_ (congrArg (fun sectionValue => (f.app U) sectionValue)
    (unit_pure (O Y) U a b)).symm
  have hu := congrArg (fun q => q.app U) (pullbackUnit_adjunction f)
  have ha := congrArg (fun q => q a) hu
  have hb := congrArg (fun q => q b) hu
  change (pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)).app U a) =
    (f.app U) a at ha
  change (pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)).app U b) =
    (f.app U) b at hb
  exact (congrArg₂ (fun a b : Γ(X,f ⁻¹ᵁ U) => a * b) ha hb).trans
    (map_mul (f.app U).hom (show Γ(Y,U) from a) (show Γ(Y,U) from b)).symm

instance unit_isIso : IsIso (hom f (O Y) (O Y)) := by
  have h := unit_compatibility f
  have hi : IsIso (hom f (O Y) (O Y) ≫
      (moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom) := by
    rw [h]
    exact ((Scheme.Modules.pullback f).mapIso (moduleTensorUnit (O Y)) ≪≫
      pullbackUnitIso f).isIso_hom
  let : IsIso (C := X.Modules)
      ((moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
        (moduleTensorUnit (O X)).hom) :=
    (moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f) ≪≫
      moduleTensorUnit (O X)).isIso_hom
  exact (isIso_comp_right_iff (C := X.Modules) _ _).mp hi

end
end MaximalSeshadri.PullbackTensor

end

end OAI
