import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorDivision
import OAI.AlgebraicGeometry.Seshadri.Sheaves.ModuleLocal
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PullbackTensorRestrict
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorUnitPure

namespace OAI


                                            
section

namespace MaximalSeshadri.PullbackTensor
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

lemma framed_isIso (M N : Y.Modules) (e : M ≅ O Y) (d : N ≅ O Y) :
    IsIso (hom f M N) := by
  have h := naturality f e.hom d.hom
  have : IsIso ((Scheme.Modules.pullback f).map (moduleTensorMap e.hom d.hom) ≫
      hom f (O Y) (O Y)) := by
    change IsIso ((Scheme.Modules.pullback f).map (moduleTensorIso e d).hom ≫ _)
    infer_instance
  have : IsIso (moduleTensorMap ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map d.hom)) := by
    change IsIso (moduleTensorIso ((Scheme.Modules.pullback f).mapIso e)
      ((Scheme.Modules.pullback f).mapIso d)).hom
    infer_instance
  have hi : IsIso (hom f M N ≫ moduleTensorMap ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map d.hom)) := h ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

instance line_isIso (L M : LineBundle Y) : IsIso (hom f L.sheaf M.sheaf) := by
  apply ModuleLocal.isIso_of_local
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨d⟩⟩ := common_affine_frames L M (f x)
  refine ⟨f ⁻¹ᵁ U.1,hx,?_⟩
  have := framed_isIso (f ∣_ U.1) _ _ e d
  have : IsIso (moduleTensorMap ((OpenBaseChange.leftSquare f U.1).hom.app L.sheaf)
      ((OpenBaseChange.leftSquare f U.1).hom.app M.sheaf)) := by
    change IsIso (moduleTensorIso ((OpenBaseChange.leftSquare f U.1).app L.sheaf)
      ((OpenBaseChange.leftSquare f U.1).app M.sheaf)).hom
    infer_instance
  have h := restrict_compatibility f U.1 L.sheaf M.sheaf
  have : IsIso ((OpenBaseChange.leftSquare f U.1).hom.app (moduleTensor Y L.sheaf M.sheaf) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map (hom f L.sheaf M.sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U.1) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj M.sheaf)).hom) := by rw [h]; infer_instance
  have hi : IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map (hom f L.sheaf M.sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U.1) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj M.sheaf)).hom) :=
    (isIso_comp_left_iff ((OpenBaseChange.leftSquare f U.1).hom.app
      (moduleTensor Y L.sheaf M.sheaf)) _).mp inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

def iso (L M : LineBundle Y) :
    (Scheme.Modules.pullback f).obj (L.tensor M).sheaf ≅
      ((L.pullback f).tensor (M.pullback f)).sheaf :=
  @asIso X.Modules _ _ _ (hom f L.sheaf M.sheaf) (line_isIso f L M)

def powIso (L : LineBundle Y) : ∀ n : ℕ,
    (Scheme.Modules.pullback f).obj (L.pow n).sheaf ≅ ((L.pullback f).pow n).sheaf
  | 0 => pullbackUnitIso f
  | n+1 => iso f L (L.pow n) ≪≫ moduleTensorIso (Iso.refl _) (powIso L n)

end
end MaximalSeshadri.PullbackTensor

end

end OAI
