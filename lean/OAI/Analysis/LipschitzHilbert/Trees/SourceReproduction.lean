import OAI.Analysis.LipschitzHilbert.Fourier.SchwartzDilation
import OAI.Analysis.LipschitzHilbert.Packets.SchwartzPacketDecay
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace OAI

/-! Actual Schwartz reproducing kernels for the long-tree frequency
rectangles. A smooth compact-frequency cutoff is constructed, rather
than adding a reproduction hypothesis to the tree estimate. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform Convolution
namespace LipschitzHilbert

/-- A smooth frequency cutoff equal to one throughout the prescribed
closed interval. Its inverse transform is a Schwartz reproducing kernel. -/
theorem exists_schwartz_reproducing_kernel (R : ℝ) (hR : 0<R) :
    ∃ K : SchwartzMap ℝ ℂ, ∀ ξ, |ξ|≤R → 𝓕 K ξ=1 := by
  let b : ContDiffBump (0:ℝ) := ⟨R,2*R,hR,by linarith⟩
  let chi : SchwartzMap ℝ ℂ :=
    (b.hasCompactSupport.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  refine ⟨𝓕⁻ chi,?_⟩
  intro ξ hξ
  rw [fourier_fourierInv_eq]
  change (b ξ : ℂ)=1
  rw [b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hξ)]
  norm_num

/-- Exact convolution reproduction from the original Fourier support. -/
theorem schwartz_convolution_reproduction (K f : SchwartzMap ℝ ℂ)
    (hK : ∀ ξ, 𝓕 f ξ≠0 → 𝓕 K ξ=1) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K f=f := by
  have hprod : SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 K) (𝓕 f)=𝓕 f := by
    ext ξ
    change 𝓕 K ξ*𝓕 f ξ=𝓕 f ξ
    by_cases hzero : 𝓕 f ξ=0
    · rw [hzero,mul_zero]
    · rw [hK ξ hzero,one_mul]
  calc
    _ = 𝓕⁻ (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K f)) := by simp
    _ = 𝓕⁻ (𝓕 f) := by rw [SchwartzMap.fourier_convolution,hprod]
    _ = f := by simp

theorem schwartz_integral_reproduction (K f : SchwartzMap ℝ ℂ)
    (hK : ∀ ξ, 𝓕 f ξ≠0 → 𝓕 K ξ=1) (x : ℝ) :
    f x=∫ y, K y*f (x-y) := by
  have h := congrArg (fun g : SchwartzMap ℝ ℂ => g x)
    (schwartz_convolution_reproduction K f hK)
  rw [SchwartzMap.convolution_apply,convolution_def] at h
  exact h.symm

/-- The normalized spatial dilation has the correct scale and mass
factor for frequency cutoffs at scale `1/r`. -/
def scaledReproducingKernel (K : SchwartzMap ℝ ℂ) (r : ℝ) (hr : 0<r) :
    SchwartzMap ℝ ℂ := r⁻¹ • schwartzDilation K r⁻¹ (inv_ne_zero hr.ne')

@[simp] theorem scaledReproducingKernel_apply (K : SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : 0<r) (x : ℝ) :
    scaledReproducingKernel K r hr x=(r⁻¹:ℂ)*K (x/r) := by
  simp only [scaledReproducingKernel,smul_apply,schwartzDilation_apply,
    Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv]
  rw [mul_comm r⁻¹ x]

theorem scaledReproducingKernel_fourier (K : SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : 0<r) (ξ : ℝ) :
    𝓕 (scaledReproducingKernel K r hr) ξ=𝓕 K (r*ξ) := by
  simp only [scaledReproducingKernel,fourier_smul,smul_apply,
    schwartzDilation_fourier,inv_inv,abs_of_pos hr]
  rw [smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
  congr 1
  field_simp

/-- Every fixed Schwartz seminorm gives the scale-invariant polynomial
kernel tail used in the cell-supremum estimate. -/
theorem scaledReproducingKernel_envelope (K : SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : 0<r) (n : ℕ) (x : ℝ) :
    ‖scaledReproducingKernel K r hr x‖≤
      (schwartzEnvelopeConstant K n/r)*lineEnvelope 0 r n x := by
  rw [scaledReproducingKernel_apply,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hr]
  have h := mul_le_mul_of_nonneg_left (schwartz_lineEnvelope_bound K n (x/r))
    (inv_nonneg.mpr hr.le)
  convert h using 1
  simp only [lineEnvelope,sub_zero,div_eq_mul_inv]
  ring

theorem scaledReproducingKernel_reproduction (K f : SchwartzMap ℝ ℂ)
    (R r : ℝ) (hr : 0<r) (hK : ∀ ξ, |ξ|≤R → 𝓕 K ξ=1)
    (hf : ∀ ξ, 𝓕 f ξ≠0 → |ξ|≤R/r) (x : ℝ) :
    f x=∫ y, scaledReproducingKernel K r hr y*f (x-y) := by
  apply schwartz_integral_reproduction
  intro ξ hξ
  rw [scaledReproducingKernel_fourier]
  apply hK
  rw [abs_mul,abs_of_pos hr]
  have h := (le_div_iff₀ hr).mp (hf ξ hξ)
  nlinarith

end LipschitzHilbert

end

end OAI
