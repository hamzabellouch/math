import Mathlib

namespace OAI

open MeasureTheory FourierTransform
open scoped FourierTransform Real
namespace Ostmann.HybridSieve

noncomputable def fourierPhase (x t : ℝ) : ℂ := Real.fourierChar (-(x*t))

lemma norm_fourierPhase (x t : ℝ) : ‖fourierPhase x t‖ = 1 := by
  simp [fourierPhase]

lemma fourier_translate (f : SchwartzMap ℝ ℂ) (x t : ℝ) :
    𝓕 (f.compSubConstCLM ℂ x) t = fourierPhase x t * 𝓕 f t := by
  have h := congrFun (Fourier.fourierIntegral_comp_add_right Real.fourierChar
    volume (f : ℝ → ℂ) (-x)) t
  simpa only [SchwartzMap.fourier_coe, Real.fourier_real_eq, SchwartzMap.compSubConstCLM_apply,
    Fourier.fourierIntegral_def, Function.comp_apply, sub_eq_add_neg,
    neg_mul, Circle.smul_def, smul_eq_mul, fourierPhase] using h

noncomputable def fourierPacket {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ∑ j ∈ s, a j • f.compSubConstCLM ℂ (freq j)

lemma fourierPacket_apply {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    fourierPacket s a freq f x = ∑ j ∈ s, a j * f (x-freq j) := by
  simp [fourierPacket, SchwartzMap.compSubConstCLM_apply]

lemma fourier_fourierPacket {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    𝓕 (fourierPacket s a freq f) t =
      (∑ j ∈ s, a j * fourierPhase (freq j) t) * 𝓕 f t := by
  simp [fourierPacket, FourierTransform.fourier_sum, FourierTransform.fourier_smul,
    fourier_translate, Finset.sum_mul, mul_assoc]

lemma fourierPacket_plancherel {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) (f : SchwartzMap ℝ ℂ) :
    (∫ t : ℝ, ‖∑ j ∈ s, a j * fourierPhase (freq j) t‖^2 * ‖𝓕 f t‖^2) =
      ∫ x : ℝ, ‖∑ j ∈ s, a j * f (x-freq j)‖^2 := by
  simpa only [fourier_fourierPacket, fourierPacket_apply, norm_mul, mul_pow]
    using SchwartzMap.integral_norm_sq_fourier (fourierPacket s a freq f)

end Ostmann.HybridSieve

end OAI
