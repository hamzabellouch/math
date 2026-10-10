import OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator

namespace OAI

namespace PiExponent.GeometrySupport.IdealPullbackMap
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
variable {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (hIJ : I ≤ J.map f)

include hIJ in

theorem comp_quotient_zero :
    (closedInclusion I ≫ structureMap f) ≫
      (Scheme.Modules.pushforward f).map (structureMap J.subschemeι) = 0 := by
  apply hom_ext_affine
  intro U
  ext x
  have hr : (closedInclusion I).app U.1 x ∈ I.ideal U := by
    rw [← closed_image I U]
    exact ⟨x, rfl⟩
  let r : Γ(X, U.1) := (closedInclusion I).app U.1 x
  have hz : r ∈ (J.subschemeι ≫ f).ker.ideal U := (hIJ U) hr
  rw [Scheme.Hom.ker_apply] at hz
  change (J.subschemeι ≫ f).app U.1 r = 0 at hz
  rw [Scheme.Hom.comp_app] at hz
  exact hz

def map : closedModule I ⟶ (Scheme.Modules.pushforward f).obj (closedModule J) :=
  kernel.lift ((Scheme.Modules.pushforward f).map (structureMap J.subschemeι))
    (closedInclusion I ≫ structureMap f) (comp_quotient_zero f I J hIJ) ≫
      (PreservesKernel.iso (Scheme.Modules.pushforward f) (structureMap J.subschemeι)).inv

@[reassoc (attr := simp)] theorem map_inclusion :
    map f I J hIJ ≫ (Scheme.Modules.pushforward f).map (closedInclusion J) =
      closedInclusion I ≫ structureMap f := by
  rw [map]
  erw [Category.assoc]
  have he : (PreservesKernel.iso (Scheme.Modules.pushforward f)
      (structureMap J.subschemeι)).inv ≫
      (Scheme.Modules.pushforward f).map (closedInclusion J) =
      kernel.ι ((Scheme.Modules.pushforward f).map (structureMap J.subschemeι)) :=
    PreservesKernel.iso_inv_ι _ _
  erw [he, kernel.lift_ι]

theorem map_app_inclusion (U : X.Opens) (s : Γ(closedModule I, U)) :
    (closedInclusion J).app (f ⁻¹ᵁ U) ((map f I J hIJ).app U s) =
      f.app U ((closedInclusion I).app U s) :=
  congrArg (fun g => g.app U s) (map_inclusion f I J hIJ)

def comap : closedModule I ⟶ (Scheme.Modules.pushforward f).obj (closedModule (I.comap f)) :=
  map f I (I.comap f) (I.le_map_comap f)

@[reassoc (attr := simp)] theorem comap_inclusion :
    comap f I ≫ (Scheme.Modules.pushforward f).map (closedInclusion (I.comap f)) =
      closedInclusion I ≫ structureMap f := map_inclusion _ _ _ _

end
end PiExponent.GeometrySupport.IdealPullbackMap

end OAI
