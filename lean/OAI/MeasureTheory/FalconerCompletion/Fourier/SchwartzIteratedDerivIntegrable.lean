import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.ComplexIteratedDerivTsupport

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

section
section
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff SchwartzMap FourierTransform RealInnerProductSpace
 theorem schwartz_iteratedDeriv_integrable (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    Integrable (iteratedDeriv n (φ : ℝ → ℂ)) := by
  apply (φ.integrable_pow_mul_iteratedFDeriv volume 0 n).mono'
    ((φ.smooth ⊤).continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).aestronglyMeasurable
  filter_upwards with x
  simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv]

noncomputable def fourierDerivativeL1 (φ : 𝓢(ℝ,ℂ)) (n : ℕ) : ℝ :=
  (∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖)/(2*Real.pi)^n

 theorem fourierDerivativeL1_nonneg (φ : 𝓢(ℝ,ℂ)) (n : ℕ) : 0 ≤ fourierDerivativeL1 φ n := by
  unfold fourierDerivativeL1
  exact div_nonneg (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)

 theorem schwartz_fourier_weighted_pointwise (φ : 𝓢(ℝ,ℂ)) (n : ℕ) (ξ : ℝ) :
    ‖ξ‖^n * ‖𝓕 φ ξ‖ ≤ fourierDerivativeL1 φ n := by
  have he := congrFun (Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (φ.smooth ⊤)
    (fun k _ => schwartz_iteratedDeriv_integrable φ k) (n := n) (by simp)) ξ
  have hh := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (iteratedDeriv n (φ : ℝ → ℂ)) ξ
  have hh' : ‖𝓕 (iteratedDeriv n (φ : ℝ → ℂ)) ξ‖ ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    simpa using! hh
  rw [he] at hh'
  simp only [norm_smul,norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one] at hh'
  have hh'' : (2*Real.pi)^n * (‖ξ‖^n*‖𝓕 φ ξ‖) ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    convert hh' using 1
    simp only [mul_pow,Real.norm_eq_abs,SchwartzMap.fourier_coe]
    ring
  exact (le_div_iff₀ (by positivity : 0 < (2*Real.pi)^n)).mpr (by simpa [mul_comm] using hh'')

end Attempt4FullFar
end
end

section
section
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff SchwartzMap FourierTransform RealInnerProductSpace
 theorem compact_derivative_integral_bound (φ : 𝓢(ℝ,ℂ)) {a b C : ℝ}
    (hab : a ≤ b) (hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a b)
    (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C) :
    (∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖) ≤ C*(b-a) := by
  have he : (∫ x in Icc a b, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖) =
      ∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply norm_eq_zero.mpr
    by_contra hn
    exact hx (hs (complex_iteratedDeriv_tsupport _ n (subset_closure hn)))
  have hh := norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    (f := fun x : ℝ => ‖iteratedDeriv n (φ : ℝ → ℂ) x‖)
    (s := Icc a b) (C := C) (by simp) (Filter.Eventually.of_forall (fun x => by simpa using hC x))
  rw [he,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hh
  simpa [Real.volume_Icc,Measure.real,ENNReal.toReal_ofReal,sub_nonneg.mpr hab] using hh

 theorem compact_fourierDerivativeL1_bound (φ : 𝓢(ℝ,ℂ)) {a b C D : ℝ}
    (hab : a ≤ b) (hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a b)
    (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C*D^n) :
    fourierDerivativeL1 φ n ≤ C*(b-a)*D^n/(2*Real.pi)^n := by
  unfold fourierDerivativeL1
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ (C*D^n)*(b-a) := compact_derivative_integral_bound φ hab hs n hC
    _ = _ := by ring

 theorem compact_smooth_to_schwartz {f : ℝ → ℂ} {a b : ℝ}
    (hs : tsupport f ⊆ Icc a b) (hf : ContDiff ℝ ∞ f) :
    ∃ φ : 𝓢(ℝ,ℂ), (φ : ℝ → ℂ) = f := by
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  exact ⟨hc.toSchwartzMap hf,rfl⟩

end Attempt4FullFar
end
end

section
section
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff SchwartzMap FourierTransform RealInnerProductSpace
 theorem compact_fourier_nonstationary {f : ℝ → ℂ} {a z C D ξ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a z) (haz : a ≤ z)
    (hξ : ξ ≠ 0) (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n f x‖ ≤ C*D^n) :
    ‖𝓕 f ξ‖ ≤ C*(z-a)*D^n/((2*Real.pi)^n*‖ξ‖^n) := by
  obtain ⟨φ,hφ⟩ := compact_smooth_to_schwartz hs hf
  have hs' : tsupport (φ : ℝ → ℂ) ⊆ Icc a z := by simpa [hφ] using hs
  have hC' : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C*D^n := by simpa [hφ] using hC
  have hh := (schwartz_fourier_weighted_pointwise φ n ξ).trans
    (compact_fourierDerivativeL1_bound φ haz hs' n hC')
  rw [SchwartzMap.fourier_coe,hφ] at hh
  have hpos : 0 < ‖ξ‖^n := pow_pos (norm_pos_iff.mpr hξ) _
  have hi : ‖𝓕 f ξ‖ ≤ (C*(z-a)*D^n/(2*Real.pi)^n)/‖ξ‖^n :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm (‖𝓕 f ξ‖)] using hh)
  simpa [div_div] using hi

 theorem compact_linear_phase_bound {f : ℝ → ℂ} {a z C D ξ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a z) (haz : a ≤ z)
    (hξ : ξ ≠ 0) (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n f x‖ ≤ C*D^n) :
    ‖∫ x : ℝ, Complex.exp (-(2:ℂ)*(Real.pi:ℂ)*Complex.I*(x:ℂ)*(ξ:ℂ))*f x‖ ≤
      C*(z-a)*D^n/((2*Real.pi)^n*‖ξ‖^n) := by
  have he : 𝓕 f ξ = ∫ x : ℝ,
      Complex.exp (-(2:ℂ)*(Real.pi:ℂ)*Complex.I*(x:ℂ)*(ξ:ℂ))*f x := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with x
    simp only [real_inner_comm ξ x, RCLike.inner_apply,conj_trivial,Complex.ofReal_mul,smul_eq_mul]
    push_cast
    congr 2
    ring
  rw [← he]
  exact compact_fourier_nonstationary hf hs haz hξ n hC

end Attempt4FullFar
end
end

end OAI
