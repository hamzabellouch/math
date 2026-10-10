import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections
import OAI.NumberTheory.PiExponent.Approximation.FrameSubopens
import OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers
import OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso

namespace OAI

noncomputable section
namespace PiExponent.PresentedIdealIso
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule PiExponentSeshadri.Frames
open PiExponent.SectionImageIdeal
variable {X Y : Scheme.{0}}

theorem imageIdealSheaf_idealPowerInclusion
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y) (n : ℕ)
    [J.sheaf.IsQuasicoherent] [(J.pow n).sheaf.IsQuasicoherent] :
    imageIdealSheaf (idealPowerInclusion J ι n) = (imageIdealSheaf ι)^n := by
  classical
  have hlocal (y : Y) : ∃ U : Y.affineOpens, y ∈ U.1 ∧
      Nonempty (J.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) := by
    obtain ⟨V, hyV, ⟨e⟩⟩ := J.locallyRankOne y
    obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset hyV
    exact ⟨⟨U,hU⟩,hyU,⟨restrictOpenFrame hUV e⟩⟩
  choose U hy he using hlocal
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    let e := Classical.choice (he y)
    rw [Scheme.IdealSheafData.ideal_pow]
    change (imageIdealSheaf (idealPowerInclusion J ι n)).ideal (U y) =
      ((imageIdealSheaf ι).ideal (U y))^n
    erw [imageIdealSheaf_on_frame (idealPowerInclusion J ι n) (U y)
        (idealPowerFrame J (U y).1 e n),
      imageIdealSheaf_on_frame ι (U y) e]
    exact idealPowerInclusion_ideal J ι (U y) e n

theorem idealPower_presents
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) (n : ℕ) :
    PresentsPullbackIdeal (I^n) f (J.pow n) (idealPowerInclusion J ι n) := by
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation J
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation (J.pow n)
  let : J.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData J.sheaf).choose.isQuasicoherent
  let : (J.pow n).sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (J.pow n).sheaf).choose.isQuasicoherent
  let : Mono ι := hJ.1
  refine ⟨@idealPowerInclusion_mono Y J ι hJ.1 n, ?_⟩
  intro U V hUV
  have h := imageIdealSheaf_idealPowerInclusion J ι n
  rw [imageIdealSheaf_eq_comap I f J ι hJ,
    ← PiExponentSeshadri.IdealPullback.comap_pow] at h
  have hu := congrArg (fun K : Y.IdealSheafData => K.ideal U) h
  exact hu.trans (PiExponentSeshadri.IdealPullback.comap_ideal (I^n) f U V hUV)

def powerIso
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) (n : ℕ) :
    (J.pow n).sheaf ≅ closedModule ((I^n).comap f) :=
  @asIso Y.Modules _ _ _
    (toIdealModule (I^n) f (J.pow n) (idealPowerInclusion J ι n)
      (idealPower_presents I f J ι hJ n))
    (toIdealModule_isIso (I^n) f (J.pow n) (idealPowerInclusion J ι n)
      (idealPower_presents I f J ι hJ n))

@[reassoc (attr := simp)] theorem powerIso_hom_inclusion
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) (n : ℕ) :
    (powerIso I f J ι hJ n).hom ≫ closedInclusion ((I^n).comap f) =
      idealPowerInclusion J ι n :=
  toIdealModule_inclusion (I^n) f (J.pow n) (idealPowerInclusion J ι n)
    (idealPower_presents I f J ι hJ n)

end PiExponent.PresentedIdealIso

end

end OAI
