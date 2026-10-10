import OAI.Analysis.LipschitzHilbert.Trees.SourceVectorSlices
import OAI.Analysis.LipschitzHilbert.Trees.SourcePlanarKernelBound

namespace OAI

/-! A product reproducing formula for general Hilbert-valued planar
Schwartz packets, derived from their two actual coordinate spectra. -/
noncomputable section
open MeasureTheory FourierTransform
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

theorem vector_scaled_integral_reproduction
    (K : SchwartzMap ℝ ℂ) (f : SchwartzMap ℝ (EuclideanSpace ℂ κ))
    (R r : ℝ) (hr : 0<r) (hK : ∀ ξ, |ξ|≤R → 𝓕 K ξ=1)
    (hf : ∀ ξ, 𝓕 f ξ≠0 → |ξ|≤R/r) (x : ℝ) :
    f x=∫ y, scaledReproducingKernel K r hr (x-y) • f y := by
  apply vector_schwartz_integral_reproduction
  intro ξ hξ
  rw [scaledReproducingKernel_fourier]
  apply hK
  rw [abs_mul,abs_of_pos hr]
  have h := (le_div_iff₀ hr).mp (hf ξ hξ)
  nlinarith

theorem planar_vector_integral_reproduction
    (Kx Ky : SchwartzMap ℝ ℂ) (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (Rx Ry rx ry : ℝ) (hrx : 0<rx) (hry : 0<ry)
    (hKx : ∀ ξ, |ξ|≤Rx → 𝓕 Kx ξ=1) (hKy : ∀ η, |η|≤Ry → 𝓕 Ky η=1)
    (hFx : ∀ y ξ, 𝓕 (vectorHorizontalSlice f y) ξ≠0 → |ξ|≤Rx/rx)
    (hFy : ∀ x η, 𝓕 (vectorVerticalSlice f x) η≠0 → |η|≤Ry/ry)
    (x y : ℝ) :
    f (x,y)=∫ p, (scaledReproducingKernel Kx rx hrx (x-p.1)*
      scaledReproducingKernel Ky ry hry (y-p.2)) • f p ∂volume.prod volume := by
  let A := scaledReproducingKernel Kx rx hrx
  let B := scaledReproducingKernel Ky ry hry
  let M := SchwartzMap.seminorm ℝ 0 0 f
  have hiA : Integrable (fun s => A (x-s)) := A.integrable.comp_sub_left x
  have hiB : Integrable (fun t => B (y-t)) := B.integrable.comp_sub_left y
  have hmajor : Integrable (fun p : ℝ×ℝ => (‖A (x-p.1)‖*‖B (y-p.2)‖)*M)
      (volume.prod volume) := (hiA.norm.mul_prod hiB.norm).mul_const M
  have hi : Integrable (fun p : ℝ×ℝ => (A (x-p.1)*B (y-p.2)) • f p)
      (volume.prod volume) := by
    apply hmajor.mono' (by fun_prop)
    filter_upwards [] with p
    rw [norm_smul,norm_mul]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f p)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    _ = ∫ s, A (x-s) • f (s,y) := by
      simpa only [vectorHorizontalSlice_apply] using
        vector_scaled_integral_reproduction Kx (vectorHorizontalSlice f y) Rx rx hrx hKx (hFx y) x
    _ = ∫ s, A (x-s) • ∫ t, B (y-t) • f (s,t) := by
      apply integral_congr_ae
      filter_upwards [] with s
      congr 1
      simpa only [vectorVerticalSlice_apply] using
        vector_scaled_integral_reproduction Ky (vectorVerticalSlice f s) Ry ry hry hKy (hFy s) y
    _ = ∫ s, ∫ t, (A (x-s)*B (y-t)) • f (s,t) := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [←integral_smul]
      simp only [smul_smul]
    _ = _ := (integral_prod _ hi).symm

/-- Moving the evaluation point within one kernel scale changes the
positive envelope by at most a factor four. -/
theorem lineEnvelope_move_center (c x r s : ℝ) (hr : 0<r) (hx : |x-c|≤r) :
    lineEnvelope x r 1 s≤4*lineEnvelope c r 1 s := by
  have h := polynomial_base_le s x c r r hr hr le_rfl hx
  simp only [lineEnvelope,pow_one,inv_eq_one_div]
  have hA : 0<1+((s-x)/r)^2 := by positivity
  have hB : 0<1+((s-c)/r)^2 := by positivity
  rw [mul_one_div,div_le_div_iff₀ hA hB]
  simpa only [div_pow,one_mul] using h

theorem scaledReproducingKernel_shifted_bound (K : SchwartzMap ℝ ℂ)
    (r c x s : ℝ) (hr : 0<r) (hx : |x-c|≤r) :
    ‖scaledReproducingKernel K r hr (x-s)‖≤
      (4*schwartzEnvelopeConstant K 1)*normalizedLineEnvelope c r s := by
  have hC := (schwartzEnvelopeConstant_pos K 1).le
  have h := scaledReproducingKernel_envelope K r hr 1 (x-s)
  have heq : lineEnvelope 0 r 1 (x-s)=lineEnvelope x r 1 s := by
    simp only [lineEnvelope,sub_zero,div_pow,sub_sq_comm]
  rw [heq] at h
  calc
    _ ≤ (schwartzEnvelopeConstant K 1/r)*lineEnvelope x r 1 s := h
    _ ≤ (schwartzEnvelopeConstant K 1/r)*(4*lineEnvelope c r 1 s) :=
      mul_le_mul_of_nonneg_left (lineEnvelope_move_center c x r s hr hx) (div_nonneg hC hr.le)
    _ = _ := by unfold normalizedLineEnvelope; ring

end LipschitzHilbert

end

end OAI
