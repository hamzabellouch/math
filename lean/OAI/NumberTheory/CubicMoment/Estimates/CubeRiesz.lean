import OAI.NumberTheory.CubicMoment.Estimates.RieszIdentity
import OAI.NumberTheory.CubicMoment.Estimates.RieszConstant
import OAI.NumberTheory.CubicMoment.Estimates.RadialCubing

namespace OAI

/-! Identification of the actual cube-lattice integral with the model term. -/

noncomputable section
open scoped SchwartzMap ContDiff
open MeasureTheory
namespace CubicFirstMoment

lemma normProfileFourier_cubing_integral (W : ℝ → ℂ) :
    (∫ z : ℂ, normProfileFourier W (z^3)) =
      (1/3:ℂ)*(∫ z : ℂ, ((‖z‖^(-(4/3:ℝ)):ℝ):ℂ)*normProfileFourier W z) := by
  have h := radial_cubing_integral (fun r => radialDualProfile W (r^2))
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with z
    rw [normProfileFourier_radial,map_pow,Complex.normSq_eq_norm_sq]
    congr 1
    ring
  · congr 1
    apply integral_congr_ae
    filter_upwards with z
    rw [normProfileFourier_radial,Complex.normSq_eq_norm_sq]

/-- The exact Riesz constant for the trace pairing and covolume-one
Eisenstein measure. All Fourier and singular-integral steps are proved. -/
theorem cubeProfileIntegral_eq_model (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    cubeProfileIntegral W = (cStar^2:ℝ) •
      ((2/Real.sqrt 3:ℝ) • (∫ z : ℂ, ((‖z‖^(-(2/3:ℝ)):ℝ):ℂ)*W (Complex.normSq z))) := by
  let F := normProfileSchwartz W hW hW' 1 (by norm_num)
  let ρ : ℝ := 2/Real.sqrt 3
  let C : ℝ := Real.pi*(4*Real.pi^2)^(-(1/3:ℝ))*Real.Gamma (1/3:ℝ)/Real.Gamma (2/3:ℝ)
  let J := ∫ z : ℂ, ((‖z‖^(-(2/3:ℝ)):ℝ):ℂ)*F z
  have hF (z : ℂ) : F z = W (Complex.normSq z) := by simp [F]
  have hFT (z : ℂ) : normProfileFourier W z = (ρ:ℂ)*traceFourier F z := by
    change (2/Real.sqrt 3:ℝ) • traceFourier (fun z => W (Complex.normSq z)) z = _
    rw [Complex.real_smul]
    congr 1
    apply congrArg (fun f : ℂ → ℂ => traceFourier f z)
    funext x
    exact (hF x).symm
  have htr : (∫ z : ℂ, ((‖z‖^(-(4/3:ℝ)):ℝ):ℂ)*traceFourier F z) = (C:ℂ)*J := by
    have h := riesz_trace_identity F
    have hg : (Real.Gamma (2/3:ℝ):ℂ) ≠ 0 := by
      exact_mod_cast (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 2/3)).ne'
    apply (mul_left_cancel₀ hg)
    dsimp only [C,J]
    rw [h]
    push_cast
    field_simp
  have hw : (∫ z : ℂ, ((‖z‖^(-(4/3:ℝ)):ℝ):ℂ)*normProfileFourier W z) =
      (ρ:ℂ)*(∫ z : ℂ, ((‖z‖^(-(4/3:ℝ)):ℝ):ℂ)*traceFourier F z) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    rw [hFT]
    ring
  have hr : (1/3:ℝ)*ρ*C = cStar^2 := by
    dsimp only [ρ,C]
    convert cubic_riesz_gaussian_constant using 1; ring
  have hc : (1/3:ℂ)*(ρ:ℂ)*(C:ℂ) = ((cStar^2:ℝ):ℂ) := by
    have hh := congrArg Complex.ofReal hr
    push_cast at hh
    simpa only [Complex.ofReal_pow] using hh
  unfold cubeProfileIntegral
  rw [Complex.real_smul,normProfileFourier_cubing_integral,hw,htr]
  change (ρ:ℂ)*((1/3:ℂ)*((ρ:ℂ)*((C:ℂ)*J))) = _
  calc
    _ = ((cStar^2:ℝ):ℂ)*(ρ:ℂ)*J := by rw [← hc]; ring
    _ = _ := by
      simp only [Complex.real_smul]
      dsimp only [ρ,J]
      simp_rw [hF]
      ring

end CubicFirstMoment

end

end OAI
