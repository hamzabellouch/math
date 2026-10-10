import OAI.Analysis.LipschitzHilbert.Fourier.HilbertCutoffNormalization
import OAI.Analysis.LipschitzHilbert.Fourier.SchwartzDilation
import OAI.Analysis.LipschitzHilbert.Fourier.SchwartzProfileBounds

namespace OAI

/-! The actual annular inverse Fourier kernel telescopes to a normalized
Schwartz profile. This gives a uniform sharp truncation comparison. -/
noncomputable section
open MeasureTheory FourierTransform LineDeriv
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def hilbertTimeKernel : SchwartzMap ℝ ℂ := 𝓕⁻ hilbertAnnularSymbol

def hilbertTimeProfile : SchwartzMap ℝ ℂ := (1/2:ℂ) • (𝓕⁻ hilbertCutoffDerivative)

theorem hilbertTimeProfile_zero : hilbertTimeProfile 0= -1 := by
  change (1/2:ℂ)*(𝓕⁻ hilbertCutoffDerivative : SchwartzMap ℝ ℂ) 0= -1
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq]
  simp only [inner_zero_right,Real.fourierChar.map_zero_eq_one,one_smul]
  rw [hilbertCutoffDerivative_integral]
  norm_num

theorem schwartzDilation_fourierInv (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : 0<r) (t : ℝ) :
    (𝓕⁻ (schwartzDilation f r hr.ne') : SchwartzMap ℝ ℂ) t=
      (r⁻¹:ℂ)*(𝓕⁻ f : SchwartzMap ℝ ℂ) (t/r) := by
  simp only [SchwartzMap.fourierInv_coe,Real.fourierInv_eq_fourier_neg]
  rw [←SchwartzMap.fourier_coe,schwartzDilation_fourier]
  rw [abs_of_pos (inv_pos.mpr hr),Complex.real_smul,neg_div]
  simp only [Complex.ofReal_inv,SchwartzMap.fourier_coe]

theorem schwartz_fourierInv_deriv (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    (𝓕⁻ (SchwartzMap.derivCLM ℂ ℂ f) : SchwartzMap ℝ ℂ) t=
      -(2*Real.pi*Complex.I)*(t:ℂ)*(𝓕⁻ f : SchwartzMap ℝ ℂ) t := by
  have heq : SchwartzMap.derivCLM ℂ ℂ f=∂_{(1:ℝ)} f := by
    ext x
    rw [SchwartzMap.derivCLM_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv]
  rw [heq,SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [smul_apply,Real.inner_apply,mul_one,smul_eq_mul]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (show (fun x : ℝ => x).HasTemperateGrowth from by fun_prop)]
  simp only [Complex.real_smul]
  ring

theorem hilbertTimeKernel_profile (t : ℝ) :
    (t:ℂ)*hilbertTimeKernel t=hilbertTimeProfile t-hilbertTimeProfile (t/2) := by
  have hd : SchwartzMap.derivCLM ℂ ℂ hilbertAnnularSymbol=
      (-(Real.pi:ℂ)*Complex.I) • (hilbertCutoffDerivative-
        (2:ℂ) • schwartzDilation hilbertCutoffDerivative 2 (by norm_num)) := by
    ext x
    simp only [SchwartzMap.derivCLM_apply,smul_apply,sub_apply,smul_eq_mul,
      schwartzDilation_apply]
    exact hilbertAnnularSymbol_deriv x
  have h := schwartz_fourierInv_deriv hilbertAnnularSymbol t
  rw [hd] at h
  simp only [sub_eq_add_neg,fourierInv_add,fourierInv_neg,fourierInv_smul,
    smul_apply,add_apply,neg_apply,smul_eq_mul] at h
  rw [schwartzDilation_fourierInv hilbertCutoffDerivative 2 (by norm_num) t] at h
  change (t:ℂ)*(𝓕⁻ hilbertAnnularSymbol : SchwartzMap ℝ ℂ) t=
    (1/2:ℂ)*(𝓕⁻ hilbertCutoffDerivative : SchwartzMap ℝ ℂ) t-
      (1/2:ℂ)*(𝓕⁻ hilbertCutoffDerivative : SchwartzMap ℝ ℂ) (t/2)
  have hp : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  apply (mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num : (-2:ℂ)≠0) hp) Complex.I_ne_zero))
  calc
    _ = -(2*Real.pi*Complex.I)*(t:ℂ)*(𝓕⁻ hilbertAnnularSymbol : SchwartzMap ℝ ℂ) t := by ring
    _ = _ := h.symm
    _ = _ := by push_cast; ring

theorem hilbertTimeKernel_sharp_integral :
    ∃ B : ℝ, 0≤B ∧ ∀ (N : ℕ) (topLength : ℝ), 0<topLength →
      Integrable (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel hilbertTimeKernel N topLength t) ∧
      (∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel hilbertTimeKernel N topLength t‖)≤B :=
  schwartzFiniteTimeKernel_sharp_integral hilbertTimeKernel hilbertTimeProfile
    hilbertTimeProfile_zero hilbertTimeKernel_profile

end LipschitzHilbert.PacketRepresentation

end

end OAI
