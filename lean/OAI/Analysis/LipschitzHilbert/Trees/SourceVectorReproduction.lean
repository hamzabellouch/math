import OAI.Analysis.LipschitzHilbert.Trees.SourceReproduction
import OAI.Analysis.LipschitzHilbert.Trees.SourceKernelIntegral

namespace OAI

/-! Reproduction estimates for the actual Hilbert-valued packets, with
constants independent of the number of Hilbert coordinates. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped Convolution
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

/-- Scalar convolution reproduces a vector Schwartz function on its
original Fourier support. -/
theorem vector_schwartz_convolution_reproduction
    (K : SchwartzMap ℝ ℂ) (f : SchwartzMap ℝ (EuclideanSpace ℂ κ))
    (hK : ∀ ξ, 𝓕 f ξ≠0 → 𝓕 K ξ=1) :
    SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) K f=f := by
  have hprod : SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) (𝓕 K) (𝓕 f)=𝓕 f := by
    ext ξ k
    have h : 𝓕 K ξ • 𝓕 f ξ=𝓕 f ξ := by
      by_cases hzero : 𝓕 f ξ=0
      · rw [hzero,smul_zero]
      · rw [hK ξ hzero,one_smul]
    exact congrArg (fun v : EuclideanSpace ℂ κ => v k) h
  calc
    _ = 𝓕⁻ (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) K f)) := by simp
    _ = 𝓕⁻ (𝓕 f) := by rw [SchwartzMap.fourier_convolution,hprod]
    _ = f := by simp

/-- The symmetric integral formula places the packet norm under a
positive scalar kernel. -/
theorem vector_schwartz_integral_reproduction
    (K : SchwartzMap ℝ ℂ) (f : SchwartzMap ℝ (EuclideanSpace ℂ κ))
    (hK : ∀ ξ, 𝓕 f ξ≠0 → 𝓕 K ξ=1) (x : ℝ) :
    f x=∫ y, K (x-y) • f y := by
  have h := congrArg (fun g : SchwartzMap ℝ (EuclideanSpace ℂ κ) => g x)
    (vector_schwartz_convolution_reproduction K f hK)
  rw [SchwartzMap.convolution_apply,←convolution_flip,convolution_def] at h
  exact h.symm

/-- Uniform local reproduction for every member of a vector family,
from one common scalar norm majorant. The null set is common to the
whole family and to all spatial evaluation points. -/
theorem vector_family_reproduction_bound {ι : Type*}
    (K : SchwartzMap ℝ ℂ) (R : ℝ) (r : ι → ℝ) (hr : ∀ a, 0<r a)
    (hK : ∀ ξ, |ξ|≤R → 𝓕 K ξ=1)
    (F : ι → SchwartzMap ℝ (EuclideanSpace ℂ κ))
    (hfreq : ∀ a ξ, 𝓕 (F a) ξ≠0 → |ξ|≤R/(r a))
    (U : ℝ → ℝ) (hUm : Measurable U) (hU2 : MemLp U 2 volume)
    (hU0 : ∀ x, 0≤U x) (B : ℝ) (hUb : ∀ x, ‖U x‖≤B)
    (hFU : ∀ a x, ‖F a x‖≤U x) :
    ∀ᵐ z ∂volume, ∀ a x, |x-z|≤r a →
      ‖F a x‖≤(96*schwartzEnvelopeConstant K 1)*DyadicLineGrid.threeGridMaximal U z := by
  filter_upwards [kernel_integral_le_threeGridMaximal U hUm hU2 B hU0 hUb] with z hz
  intro a x hxz
  let s := r a
  have hs : 0<s := hr a
  have hmult (ξ : ℝ) (hξ : 𝓕 (F a) ξ≠0) :
      𝓕 (scaledReproducingKernel K s hs) ξ=1 := by
    rw [scaledReproducingKernel_fourier]
    apply hK
    rw [abs_mul,abs_of_pos hs]
    have h := (le_div_iff₀ hs).mp (hfreq a ξ hξ)
    nlinarith
  rw [vector_schwartz_integral_reproduction (scaledReproducingKernel K s hs) (F a) hmult x]
  let C := schwartzEnvelopeConstant K 1
  have hC : 0≤C := (schwartzEnvelopeConstant_pos K 1).le
  have hki : Integrable (fun y => s⁻¹*lineEnvelope x s 1 y*U y) :=
    ((integrable_lineEnvelope_one x s hs).const_mul s⁻¹).mul_bdd
      hUm.aestronglyMeasurable (Filter.Eventually.of_forall hUb)
  calc
    _ ≤ ∫ y, C*(s⁻¹*lineEnvelope x s 1 y*U y) := by
      apply norm_integral_le_of_norm_le (hki.const_mul C)
      filter_upwards [] with y
      rw [norm_smul]
      have he := scaledReproducingKernel_envelope K s hs 1 (x-y)
      have heq : lineEnvelope 0 s 1 (x-y)=lineEnvelope x s 1 y := by
        simp only [lineEnvelope,sub_zero,div_pow,sub_sq_comm]
      rw [heq] at he
      calc
        _ ≤ ((C/s)*lineEnvelope x s 1 y)*U y :=
          mul_le_mul he (hFU a y) (norm_nonneg _) (mul_nonneg (div_nonneg hC hs.le) (lineEnvelope_nonneg _ _ _ _))
        _ = _ := by ring
    _ = C*∫ y, s⁻¹*lineEnvelope x s 1 y*U y := integral_const_mul _ _
    _ ≤ C*(96*DyadicLineGrid.threeGridMaximal U z) :=
      mul_le_mul_of_nonneg_left (hz x s hs (by simpa only [abs_sub_comm] using hxz)) hC
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
