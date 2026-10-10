import OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma restrictedInclusion_structureMap_eq_zero (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    restrictedInclusion I f ≫ structureMap (I.comap f).subschemeι = 0 := by
  apply hom_ext_affine
  intro U
  ext x
  change (I.comap f).subschemeι.app U.1 ((restrictedInclusion I f).app U.1 x) = 0
  apply RingHom.mem_ker.mp
  rw [(I.comap f).ker_subschemeι_app U, ← restricted_image I f U]
  exact ⟨x,rfl⟩

def restrictedToClosed (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (closedModule I).restrict f ⟶ closedModule (I.comap f) :=
  kernel.lift (structureMap (I.comap f).subschemeι) (restrictedInclusion I f)
    (restrictedInclusion_structureMap_eq_zero I f)

@[reassoc (attr := simp)] lemma restrictedToClosed_inclusion (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    restrictedToClosed I f ≫ closedInclusion (I.comap f) = restrictedInclusion I f :=
  kernel.lift_ι _ _ _

instance restrictedToClosed_isIso (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    IsIso (restrictedToClosed I f) := by
  apply isIso_of_affine_app
  intro U
  let : Mono (closedInclusion (I.comap f)).val := inferInstanceAs
    (Mono ((Scheme.Modules.toPresheafOfModules X).map (closedInclusion (I.comap f))))
  let : Mono (restrictedInclusion I f).val := inferInstanceAs
    (Mono ((Scheme.Modules.toPresheafOfModules X).map (restrictedInclusion I f)))
  have ht : Function.Injective ((closedInclusion (I.comap f)).app U.1) := by
    exact PresheafOfModules.injective_of_mono (closedInclusion (I.comap f)).val (op U.1)
  have hs : Function.Injective ((restrictedInclusion I f).app U.1) := by
    exact PresheafOfModules.injective_of_mono (restrictedInclusion I f).val (op U.1)
  have he (x : Γ((closedModule I).restrict f,U.1)) :
      (closedInclusion (I.comap f)).app U.1 ((restrictedToClosed I f).app U.1 x) =
        (restrictedInclusion I f).app U.1 x :=
    congrArg (fun g => g.app U.1 x) (restrictedToClosed_inclusion I f)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    apply hs
    rw [← he x, ← he y, h]
  · intro x
    have hx : (closedInclusion (I.comap f)).app U.1 x ∈ (I.comap f).ideal U := by
      rw [← closed_image (I.comap f) U]
      exact ⟨x,rfl⟩
    rw [← restricted_image I f U] at hx
    obtain ⟨y,hy⟩ := hx
    exact ⟨y, ht ((he y).trans hy)⟩

def closedModuleRestrictIso (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (closedModule I).restrict f ≅ closedModule (I.comap f) := asIso (restrictedToClosed I f)

lemma closedModuleRestrictIso_naturality {I J : Y.IdealSheafData} (h : I ≤ J)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).map (closedMap h) ≫ (closedModuleRestrictIso J f).hom =
      (closedModuleRestrictIso I f).hom ≫ closedMap (Scheme.IdealSheafData.comap_mono f h) := by
  apply (cancel_mono (closedInclusion (J.comap f))).mp
  simp only [Category.assoc, closedMap_inclusion]
  change (Scheme.Modules.restrictFunctor f).map (closedMap h) ≫
    restrictedToClosed J f ≫ closedInclusion (J.comap f) =
    restrictedToClosed I f ≫ closedInclusion (I.comap f)
  rw [restrictedToClosed_inclusion, restrictedToClosed_inclusion]
  unfold restrictedInclusion
  let F : Y.Modules ⥤ X.Modules := Scheme.Modules.restrictFunctor f
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g : F.obj (closedModule I) ⟶ F.obj (unit Y) =>
      g ≫ (Scheme.Modules.restrictUnitIso f).hom)
      (F.map_comp (closedMap h) (closedInclusion J)).symm).trans
      (congrArg (fun g : closedModule I ⟶ unit Y =>
        F.map g ≫ (Scheme.Modules.restrictUnitIso f).hom) (closedMap_inclusion h)))

end
end PiExponentSeshadri.IdealModule

end OAI
