import OAI.NumberTheory.JointDickman.Counting.CoefficientProfileFreeze
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace OAI

/-! # Fourier inversion and polynomial moments for the fixed smooth profile -/

namespace JointDickman
open MeasureTheory
open scoped FourierTransform SchwartzMap

theorem testFourierTransform_eq_fourier (w : ℝ → ℝ) :
    testFourierTransform w = 𝓕 (fun s => (w s : ℂ)) := by
  funext ξ
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by
    dsimp [additivePhase]
    have he : ((2*Real.pi*(-ξ*s) : ℝ) : ℂ)*Complex.I =
        ((-2*Real.pi*s*ξ : ℝ) : ℂ)*Complex.I := by push_cast; ring
    rw [he]
    ring)

theorem schwartz_testFourier_moment (w : 𝓢(ℝ, ℝ)) (k : ℕ) :
    Integrable (fun ξ : ℝ => |ξ|^k*‖testFourierTransform w ξ‖) := by
  let f : 𝓢(ℝ, ℂ) := w.postcompCLM Complex.ofRealCLM
  have he : testFourierTransform w = (⇑(𝓕 f : 𝓢(ℝ, ℂ))) := by
    rw [testFourierTransform_eq_fourier,SchwartzMap.fourier_coe]
    rfl
  rw [he]
  simpa only [Real.norm_eq_abs] using (𝓕 f : 𝓢(ℝ, ℂ)).integrable_pow_mul volume k

theorem schwartz_testFourier_integrable (w : 𝓢(ℝ, ℝ)) :
    Integrable (testFourierTransform w) := by
  let f : 𝓢(ℝ, ℂ) := w.postcompCLM Complex.ofRealCLM
  have he : testFourierTransform w = (⇑(𝓕 f : 𝓢(ℝ, ℂ))) := by
    rw [testFourierTransform_eq_fourier,SchwartzMap.fourier_coe]
    rfl
  rw [he]
  exact (𝓕 f : 𝓢(ℝ, ℂ)).integrable

theorem schwartz_testFourier_inversion (w : 𝓢(ℝ, ℝ)) (s : ℝ) :
    (∫ ξ : ℝ, testFourierTransform w ξ*additivePhase (ξ*s)) = (w s : ℂ) := by
  let f : 𝓢(ℝ, ℂ) := w.postcompCLM Complex.ofRealCLM
  have he : testFourierTransform w = (⇑(𝓕 f : 𝓢(ℝ, ℂ))) := by
    rw [testFourierTransform_eq_fourier,SchwartzMap.fourier_coe]
    rfl
  have hh := congrFun (f.continuous.fourierInv_fourier_eq f.integrable
    (show Integrable (𝓕 (f : ℝ → ℂ)) from (𝓕 f : 𝓢(ℝ, ℂ)).integrable)) s
  rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul] at hh
  calc
    _ = ∫ ξ : ℝ, Complex.exp (((-2*Real.pi*ξ*(-s) : ℝ) : ℂ)*Complex.I)*
        (𝓕 (f : ℝ → ℂ)) ξ := by
      rw [he]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ξ => by
        dsimp [additivePhase]
        have harg : ((2*Real.pi*(ξ*s) : ℝ) : ℂ)*Complex.I =
            ((-2*Real.pi*ξ*(-s) : ℝ) : ℂ)*Complex.I := by push_cast; ring
        rw [harg]
        have hff := congrFun (SchwartzMap.fourier_coe f) ξ
        rw [hff]
        ring)
    _ = _ := by simpa only [smul_eq_mul,f,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply] using hh

end JointDickman

end OAI
