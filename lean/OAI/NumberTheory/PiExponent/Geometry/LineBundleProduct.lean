import OAI.NumberTheory.PiExponent.Approximation.FrameSubopens
import OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem common_affine_frames (L M : LineBundle X) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) ∧
      Nonempty (M.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  obtain ⟨V, hxV, ⟨d⟩⟩ := M.locallyRankOne x
  obtain ⟨W, hW, hxW, hWUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  exact ⟨⟨W, hW⟩, hxW,
    ⟨restrictOpenFrame (fun _ hx => (hWUV hx).1) e⟩,
    ⟨restrictOpenFrame (fun _ hx => (hWUV hx).2) d⟩⟩

def LineBundle.tensor (L M : LineBundle X) : LineBundle X where
  sheaf := moduleTensor X L.sheaf M.sheaf
  locallyRankOne x := by
    obtain ⟨U, hx, ⟨e⟩, ⟨d⟩⟩ := common_affine_frames L M x
    exact ⟨U.1, hx, ⟨moduleTensorRestrict U.1 L.sheaf M.sheaf ≪≫
      moduleTensorIso e d ≪≫ moduleTensorUnit (structureSheaf U.1.toScheme)⟩⟩

end Geometry

namespace PullbackTensor
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

instance line_isIso (L M : LineBundle Y) : IsIso (hom f L.sheaf M.sheaf) := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro x
  obtain ⟨U, hx, ⟨e⟩, ⟨d⟩⟩ := common_affine_frames L M (f x)
  refine ⟨f ⁻¹ᵁ U.1, hx, ?_⟩
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
  @asIso _ _ _ _ (hom f L.sheaf M.sheaf) (line_isIso f L M)

end PullbackTensor

end PiExponentSeshadri

end

end OAI
