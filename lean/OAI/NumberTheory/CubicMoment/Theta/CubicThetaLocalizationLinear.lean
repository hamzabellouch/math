import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalizationSobolevBound

namespace OAI

/-! Real linearity of the actual localized Sobolev vectors, with their
fixed compact support retained in the codomain. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance localizationLinear_borel : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance localizationLinear_borelSpace : BorelSpace CubicThetaTangent := ⟨rfl⟩

variable {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
  (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})

def localizedRealTest : cubicThetaSmoothTests →ₗ[ℝ] C1c (E:=CubicThetaTangent) where
  toFun F := realTest (cubicThetaTestLocalization φ F)
    ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
    (cubicThetaTestLocalization_compact hc F)
  map_add' F G := by
    apply Subtype.ext
    funext u
    change (cubicThetaTestLocalization φ ((F+G : cubicThetaSmoothTests) : CubicThetaSection) _).re =
      (cubicThetaTestLocalization φ F _).re+(cubicThetaTestLocalization φ G _).re
    rw [cubicThetaTestLocalization_add]
    rfl
  map_smul' c F := by
    apply Subtype.ext
    funext u
    change (cubicThetaTestLocalization φ (((c:ℂ) • F : cubicThetaSmoothTests) : CubicThetaSection) _).re =
      c*(cubicThetaTestLocalization φ F _).re
    rw [cubicThetaTestLocalization_smul]
    simp

def localizedImagTest : cubicThetaSmoothTests →ₗ[ℝ] C1c (E:=CubicThetaTangent) where
  toFun F := imagTest (cubicThetaTestLocalization φ F)
    ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
    (cubicThetaTestLocalization_compact hc F)
  map_add' F G := by
    apply Subtype.ext
    funext u
    change (cubicThetaTestLocalization φ ((F+G : cubicThetaSmoothTests) : CubicThetaSection) _).im =
      (cubicThetaTestLocalization φ F _).im+(cubicThetaTestLocalization φ G _).im
    rw [cubicThetaTestLocalization_add]
    rfl
  map_smul' c F := by
    apply Subtype.ext
    funext u
    change (cubicThetaTestLocalization φ (((c:ℂ) • F : cubicThetaSmoothTests) : CubicThetaSection) _).im =
      c*(cubicThetaTestLocalization φ F _).im
    rw [cubicThetaTestLocalization_smul]
    simp

def localizedRealH1 : cubicThetaSmoothTests →ₗ[ℝ] h1 (μ:=tangentBorelVolume) :=
  ((graph (μ:=tangentBorelVolume)).comp (localizedRealTest hφ hc hp)).codRestrict _
    (fun F => Submodule.le_topologicalClosure _ ⟨localizedRealTest hφ hc hp F,rfl⟩)

def localizedImagH1 : cubicThetaSmoothTests →ₗ[ℝ] h1 (μ:=tangentBorelVolume) :=
  ((graph (μ:=tangentBorelVolume)).comp (localizedImagTest hφ hc hp)).codRestrict _
    (fun F => Submodule.le_topologicalClosure _ ⟨localizedImagTest hφ hc hp F,rfl⟩)

def localizedRealSupported : cubicThetaSmoothTests →ₗ[ℝ] Supported (tsupport φ) hc :=
  (localizedRealH1 hφ hc hp).codRestrict _ (fun F =>
    (realSupported hc (cubicThetaTestLocalization φ F)
      ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
      (cubicThetaTestLocalization_compact hc F) tsupport_mul_subset_left).property)

def localizedImagSupported : cubicThetaSmoothTests →ₗ[ℝ] Supported (tsupport φ) hc :=
  (localizedImagH1 hφ hc hp).codRestrict _ (fun F =>
    (imagSupported hc (cubicThetaTestLocalization φ F)
      ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
      (cubicThetaTestLocalization_compact hc F) tsupport_mul_subset_left).property)

def localizedSupportedPair : cubicThetaSmoothTests →ₗ[ℝ]
    (Supported (tsupport φ) hc × Supported (tsupport φ) hc) :=
  (localizedRealSupported hφ hc hp).prod (localizedImagSupported hφ hc hp)

lemma localizedSupportedPair_norm (F : cubicThetaSmoothTests) :
    ‖localizedSupportedPair hφ hc hp F‖=‖localizedPair hφ hc hp F‖ := rfl

end CubicFirstMoment.LocalSobolev

end

end OAI
