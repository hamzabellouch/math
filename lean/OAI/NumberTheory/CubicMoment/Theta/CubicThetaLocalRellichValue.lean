import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalEnergyRellich

namespace OAI

/-! The compact local energy inclusion has the original localized
complex section as its value, rather than an unrelated Sobolev vector. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance rellichValue_borel : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance rellichValue_borelSpace : BorelSpace CubicThetaTangent := ⟨rfl⟩

lemma tangentFunction_memLp (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : MemLp (f ∘ cubicThetaTangentCoordinates) 2 tangentBorelVolume :=
  (hf.continuous.comp cubicThetaTangentCoordinates.continuous).memLp_of_hasCompactSupport
    (hc.comp_homeomorph cubicThetaTangentCoordinates.toHomeomorph)

def tangentFunctionL2 (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : TangentComplexL2 := (tangentFunction_memLp f hf hc).toLp _

theorem complexInclusion_value {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hs : tsupport f⊆K) :
    complexInclusion K hK (realSupported hK f hf hc hs,imagSupported hK f hf hc hs)=
      tangentFunctionL2 f hf hc := by
  let r := toL2 (μ:=tangentBorelVolume) (realTest f hf hc)
  let i := toL2 (μ:=tangentBorelVolume) (imagTest f hf hc)
  have hr : (r:CubicThetaTangent → ℝ)=ᵐ[tangentBorelVolume]
      fun u => (f (cubicThetaTangentCoordinates u)).re :=
    (memLp_of_mem_C1c (μ:=tangentBorelVolume) (realTest f hf hc).property).coeFn_toLp
  have hi : (i:CubicThetaTangent → ℝ)=ᵐ[tangentBorelVolume]
      fun u => (f (cubicThetaTangentCoordinates u)).im :=
    (memLp_of_mem_C1c (μ:=tangentBorelVolume) (imagTest f hf hc).property).coeFn_toLp
  change Complex.ofRealCLM.compLp r+Complex.I • Complex.ofRealCLM.compLp i=tangentFunctionL2 f hf hc
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (Complex.ofRealCLM.compLp r) (Complex.I • Complex.ofRealCLM.compLp i),
    Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLp i),
    Complex.ofRealCLM.coeFn_compLp r,Complex.ofRealCLM.coeFn_compLp i,hr,hi,
    (tangentFunction_memLp f hf hc).coeFn_toLp] with u ha hm hcr hci hru hiu hfu
  simp only [Pi.add_apply,Pi.smul_apply] at ha hm
  rw [ha,hm,hcr,hci,hru,hiu]
  change (f (cubicThetaTangentCoordinates u)).re+
    Complex.I*(f (cubicThetaTangentCoordinates u)).im=_
  change _=((tangentFunction_memLp f hf hc).toLp _) u
  rw [hfu]
  simpa only [mul_comm,Function.comp_apply] using Complex.re_add_im (f (cubicThetaTangentCoordinates u))

theorem localEnergyInclusion_test {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (F : cubicThetaSmoothTests) :
    localEnergyInclusion hφ hc hp (localEnergyTest hφ hc hp F)=
      tangentFunctionL2 (cubicThetaTestLocalization φ F)
        ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
        (cubicThetaTestLocalization_compact hc F) := by
  change complexInclusion (tsupport φ) hc
    (localEnergyToSupported hφ hc hp (localEnergyTest hφ hc hp F))=_
  rw [localEnergyToSupported_test]
  exact complexInclusion_value hc _ _ _ tsupport_mul_subset_left

end CubicFirstMoment.LocalSobolev

end

end OAI
