import OAI.Analysis.LipschitzHilbert.Fourier.ShortVerticalError
import OAI.Analysis.LipschitzHilbert.Estimates.SharpTimeMoment
import OAI.Analysis.LipschitzHilbert.Fourier.KernelDifferencePairing

namespace OAI

/-! The actual sharply truncated directional transform differs from its
horizontal counterpart by a uniformly controlled very-short-time error. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem veryShortHilbertError_identity (r R : ℝ) (hr : 0<r) (hR : 0<R) (hsmall : R≤1/4)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    shortVerticalError (sharpTimeKernel r R) u f z=
      slopeKernelOperator (sharpTimeKernel r R) u f z-
        slopeKernelOperator (sharpTimeKernel r R) (fun _ => 0) f z := by
  have hK := sharpTimeKernel_integrable r R hr hR
  unfold shortVerticalError slopeKernelOperator
  rw [←integral_sub (slope_integrand_integrable _ hK u f z)
    (slope_integrand_integrable _ hK (fun _ => 0) f z)]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : |t|≤1/4
  · simp only [ite_eq_left ht,shortVerticalDifference,mul_zero,sub_zero,mul_sub]
  · have hzero : sharpTimeKernel r R t=0 := by
      unfold sharpTimeKernel
      apply ite_eq_right
      intro h
      exact ht (h.2.le.trans hsmall)
    simp only [ite_eq_right ht,hzero,mul_zero,zero_mul,sub_self]

theorem veryShortHilbertProjection_pairing (r R : ℝ) (hr : 0<r) (hR : 0<R) (hsmall : R≤1/4)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (hub : ∀ z, |u z|≤1)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) (hg : ∀ z, ‖g z‖≤1) :
    ‖∫ z, (slopeKernelOperator (sharpTimeKernel r R) u (schwartzVerticalProjection p w 0 f) z-
      slopeKernelOperator (sharpTimeKernel r R) (fun _ => 0) (schwartzVerticalProjection p w 0 f) z)*
        star (g z) ∂planeMeasure‖≤
      (2*R*verticalProjectionCost (verticalDerivativeProfile p)/w)*
        min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  let K := sharpTimeKernel r R
  let F := schwartzVerticalProjection p w 0 f
  let M := ∫ t, |t| *‖K t‖
  let C := verticalProjectionCost (verticalDerivativeProfile p)/w
  have hC : 0≤C := div_nonneg (verticalProjectionCost_pos _).le hw.le
  have hM : 0≤M := integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hmom := sharpTimeKernel_first_moment r R hr hR
  have hsz := shortVerticalProjectionError_sizes K (sharpTimeKernel_measurable r R) hmom.1
    u hu hub p w hw f hf
  have hi := (shortVerticalError_l1 K (sharpTimeKernel_measurable r R) hmom.1 u hu hub F).1
  have h1 (z : ℝ×ℝ) : ‖shortVerticalError K u F z*star (g z)‖≤‖shortVerticalError K u F z‖ := by
    rw [norm_mul,norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (hg z)
  have h2 (z : ℝ×ℝ) : ‖shortVerticalError K u F z*star (g z)‖≤(M*C)*‖g z‖ := by
    rw [norm_mul,norm_star]
    exact mul_le_mul_of_nonneg_right (by simpa only [M,C,mul_div_assoc] using hsz.2 z) (norm_nonneg _)
  have hb1 : ‖∫ z, shortVerticalError K u F z*star (g z) ∂planeMeasure‖≤
      (M*C)*(4*∫ z, ‖f z‖ ∂planeMeasure) := by
    exact (norm_integral_le_of_norm_le hi.norm (Filter.Eventually.of_forall h1)).trans
      (hsz.1.trans_eq (by dsimp [M,C]; ring))
  have hb2 : ‖∫ z, shortVerticalError K u F z*star (g z) ∂planeMeasure‖≤
      (M*C)*(∫ z, ‖g z‖ ∂planeMeasure) := by
    have h := norm_integral_le_of_norm_le ((g.integrable (μ:=planeMeasure)).norm.const_mul (M*C))
      (Filter.Eventually.of_forall h2)
    simpa only [integral_const_mul] using h
  simp_rw [←veryShortHilbertError_identity r R hr hR hsmall]
  change ‖∫ z, shortVerticalError K u F z*star (g z) ∂planeMeasure‖≤_
  calc
    _ ≤ (M*C)*min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
      rw [mul_min_of_nonneg _ _ (mul_nonneg hM hC)]
      exact le_min hb1 hb2
    _ ≤ (2*R*C)*min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmom.2 hC)
        (le_min (by positivity) (integral_nonneg fun _ => norm_nonneg _))
    _ = _ := by dsimp [C]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
