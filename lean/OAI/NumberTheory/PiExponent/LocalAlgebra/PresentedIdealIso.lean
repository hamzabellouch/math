import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent
import OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator
import OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal

namespace OAI

noncomputable section
namespace PiExponent.PresentedIdealIso
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
open PiExponent.SectionImageIdeal
variable {X Y : Scheme.{0}}

theorem imageIdealSheaf_eq_comap
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    [J.sheaf.IsQuasicoherent] (hJ : PresentsPullbackIdeal I f J ι) :
    imageIdealSheaf ι = I.comap f := by
  classical
  have hlocal (y : Y) : ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ V : X.affineOpens, U.1 ≤ f ⁻¹ᵁ V.1 := by
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset
      (show f y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ f ⁻¹ᵁ V from hyV)
    exact ⟨⟨U, hU⟩, hyU, ⟨V, hV⟩, hUV⟩
  choose U hy V hUV using hlocal
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    exact (hJ.2 (U y) (V y) (hUV y)).trans
      (PiExponentSeshadri.IdealPullback.comap_ideal I f (U y) (V y) (hUV y)).symm

theorem presented_range_eq
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) (U : Y.affineOpens) :
    (ι.val.app (op U.1)).hom.range = (I.comap f).ideal U := by
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation J
  let : J.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData J.sheaf).choose.isQuasicoherent
  exact congrArg (fun K : Y.IdealSheafData => K.ideal U)
    (imageIdealSheaf_eq_comap I f J ι hJ)

theorem inclusion_structureMap_zero
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) :
    ι ≫ structureMap (I.comap f).subschemeι = 0 := by
  apply hom_ext_affine
  intro U
  ext x
  change (I.comap f).subschemeι.app U.1 (ι.app U.1 x) = 0
  apply RingHom.mem_ker.mp
  rw [(I.comap f).ker_subschemeι_app U, ← presented_range_eq I f J ι hJ U]
  exact ⟨x, rfl⟩

def toIdealModule
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) : J.sheaf ⟶ closedModule (I.comap f) :=
  kernel.lift (structureMap (I.comap f).subschemeι) ι
    (inclusion_structureMap_zero I f J ι hJ)

@[reassoc (attr := simp)] theorem toIdealModule_inclusion
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) :
    toIdealModule I f J ι hJ ≫ closedInclusion (I.comap f) = ι :=
  kernel.lift_ι _ _ _

instance toIdealModule_isIso
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) : IsIso (toIdealModule I f J ι hJ) := by
  have : Mono ι := hJ.1
  let K := I.comap f
  let t := toIdealModule I f J ι hJ
  let κ := closedInclusion K
  apply isIso_of_affine_app
  intro U
  have hιinj : Function.Injective (ι.val.app (op U.1)) := by
    have : Mono ι.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules Y).map ι))
    exact PresheafOfModules.injective_of_mono ι.val (op U.1)
  have hκinj : Function.Injective (κ.val.app (op U.1)) := by
    have : Mono κ.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules Y).map κ))
    exact PresheafOfModules.injective_of_mono κ.val (op U.1)
  have hfac (m : Γ(J.sheaf, U.1)) : κ.app U.1 (t.app U.1 m) = ι.app U.1 m :=
    congrArg (fun a : J.sheaf ⟶ structureSheaf Y => a.app U.1 m)
      (toIdealModule_inclusion I f J ι hJ)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply hιinj
    exact (hfac a).symm.trans ((congrArg (κ.app U.1) hab).trans (hfac b))
  · intro z
    have hz : κ.app U.1 z ∈ K.ideal U := by
      rw [← closed_image K U]
      exact ⟨z, rfl⟩
    rw [← presented_range_eq I f J ι hJ U] at hz
    obtain ⟨m, hm⟩ := hz
    refine ⟨m, hκinj ?_⟩
    exact (hfac m).trans hm

def iso
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J₁ J₂ : LineBundle Y)
    (ι₁ : J₁.sheaf ⟶ structureSheaf Y) (ι₂ : J₂.sheaf ⟶ structureSheaf Y)
    (h₁ : PresentsPullbackIdeal I f J₁ ι₁)
    (h₂ : PresentsPullbackIdeal I f J₂ ι₂) : J₁.sheaf ≅ J₂.sheaf :=
  asIso (toIdealModule I f J₁ ι₁ h₁) ≪≫ (asIso (toIdealModule I f J₂ ι₂ h₂)).symm

@[reassoc (attr := simp)] theorem iso_hom_inclusion
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J₁ J₂ : LineBundle Y)
    (ι₁ : J₁.sheaf ⟶ structureSheaf Y) (ι₂ : J₂.sheaf ⟶ structureSheaf Y)
    (h₁ : PresentsPullbackIdeal I f J₁ ι₁)
    (h₂ : PresentsPullbackIdeal I f J₂ ι₂) :
    (iso I f J₁ J₂ ι₁ ι₂ h₁ h₂).hom ≫ ι₂ = ι₁ := by
  have h₂inv : (asIso (toIdealModule I f J₂ ι₂ h₂)).inv ≫ ι₂ =
      closedInclusion (I.comap f) := by
    have hh := congrArg
      (fun a : J₂.sheaf ⟶ structureSheaf Y =>
        (asIso (toIdealModule I f J₂ ι₂ h₂)).inv ≫ a)
      (toIdealModule_inclusion I f J₂ ι₂ h₂)
    exact hh.symm.trans (Iso.inv_hom_id_assoc _ _)
  change toIdealModule I f J₁ ι₁ h₁ ≫
    (asIso (toIdealModule I f J₂ ι₂ h₂)).inv ≫ ι₂ = ι₁
  rw [h₂inv]
  exact toIdealModule_inclusion I f J₁ ι₁ h₁

end PiExponent.PresentedIdealIso

end

end OAI
