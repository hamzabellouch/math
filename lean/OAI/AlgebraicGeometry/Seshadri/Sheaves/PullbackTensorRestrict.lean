import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.OpenPullbackUnit
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorOpenSquare

namespace OAI


                                                
section

namespace MaximalSeshadri.PullbackTensor
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.TensorPure

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

@[reassoc]
lemma open_base_change_naturality {source target : X.Modules}
    (morphism : source ⟶ target) :
    (Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pushforward f).map morphism) ≫
        (OpenBaseChange.iso f U target).hom =
    (OpenBaseChange.iso f U source).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map morphism) := by
  apply Scheme.Modules.hom_ext
  intro openSet
  simp only [Scheme.Modules.Hom.comp_app]
  change morphism.app (f ⁻¹ᵁ (U.ι ''ᵁ openSet)) ≫
      (OpenBaseChange.hom f U target).app openSet =
    (OpenBaseChange.hom f U source).app openSet ≫
      morphism.app ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ openSet))
  rw [OpenBaseChange.hom_app, OpenBaseChange.hom_app]
  exact (morphism.mapPresheaf.naturality
    (eqToHom (image_morphismRestrict_preimage f U openSet)).op).symm

lemma open_transpose (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
      ((OpenBaseChange.leftSquare f U).hom.app M) =
    (Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)).hom :=
  (OpenBaseChange.unit_compatibility f U M).symm

lemma restrict_compatibility (M N : Y.Modules) :
    (OpenBaseChange.leftSquare f U).hom.app (moduleTensor Y M N) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (hom f M N) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)).hom =
    (Scheme.Modules.pullback (f ∣_ U)).map (moduleTensorRestrict U M N).hom ≫
      hom (f ∣_ U) (M.restrict U.ι) (N.restrict U.ι) ≫
      moduleTensorMap ((OpenBaseChange.leftSquare f U).hom.app M)
        ((OpenBaseChange.leftSquare f U).hom.app N) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _).injective
  conv_rhs => rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  conv_lhs => rw [Adjunction.homEquiv_naturality_right]
  rw [open_transpose]
  have ht : (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
      (hom (f ∣_ U) (M.restrict U.ι) (N.restrict U.ι)) =
      moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι))
        ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (N.restrict U.ι)) ≫
        PushforwardTensor.hom (f ∣_ U) _ _ := Equiv.apply_symm_apply _ _
  rw [ht]
  simp only [Functor.map_comp, Category.assoc]
  rw [← open_base_change_naturality_assoc]
  rw [← Functor.map_comp_assoc, unit_hom, Functor.map_comp]
  simp only [Category.assoc]
  rw [OpenBaseChange.tensor_square]
  rw [← Category.assoc]
  refine (congrArg (fun q => q ≫
    moduleTensorMap (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)).hom
      (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj N)).hom ≫
    PushforwardTensor.hom (f ∣_ U)
      (((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι)
      (((Scheme.Modules.pullback f).obj N).restrict (f ⁻¹ᵁ U).ι))
    (TensorPure.restrict_map U
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N))).trans ?_
  simp only [Category.assoc]
  rw [← moduleTensorMap_comp_assoc]
  rw [OpenBaseChange.unit_compatibility,OpenBaseChange.unit_compatibility]
  rw [moduleTensorMap_comp]
  simp only [Category.assoc]
  exact congrArg (fun q => (moduleTensorRestrict U M N).hom ≫
    moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι))
      ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (N.restrict U.ι)) ≫ q)
    (PushforwardTensor.naturality (f ∣_ U)
      ((OpenBaseChange.leftSquare f U).hom.app M) ((OpenBaseChange.leftSquare f U).hom.app N))

end
end MaximalSeshadri.PullbackTensor

end


end OAI
