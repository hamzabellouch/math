import OAI.Geometry.RCD.Harmonic.EuclideanRadialMean
import OAI.Geometry.RCD.Coordinates.GevreyConvolution

namespace OAI

/-! # Rescaled radial kernels and exact convolution normalization -/

open Set Metric Filter MeasureTheory
open scoped ContDiff Convolution

noncomputable section
namespace RegularPointCoordinates

def euclideanRadialKernel (n : ℕ) (r : ℝ) (x : Euclidean n) : ℝ :=
  euclideanRadialWeight n (r⁻¹ • x)

theorem euclideanRadialKernel_smooth (n : ℕ) (r : ℝ) :
    ContDiff ℝ ∞ (euclideanRadialKernel n r) :=
  (euclideanRadialWeight_smooth n).comp (contDiff_id.const_smul r⁻¹)

theorem euclideanRadialKernel_support (n : ℕ) {r : ℝ} (hr : 0 < r) :
    tsupport (euclideanRadialKernel n r) ⊆ closedBall 0 r := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hh := euclideanRadialWeight_support n (subset_tsupport _ hx)
  simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr)] at hh ⊢
  have hm := mul_le_mul_of_nonneg_left hh hr.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul,mul_one] using hm

theorem euclideanRadialKernel_compact (n : ℕ) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (euclideanRadialKernel n r) :=
  (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (euclideanRadialKernel_support n hr)

/-- Scaling the kernel produces precisely the dilation average, including
its Euclidean volume factor. -/
theorem convolution_radialKernel_eq (n : ℕ) (f : Euclidean n → ℝ) (p : Euclidean n)
    {r : ℝ} (hr : 0 < r) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] euclideanRadialKernel n r) p =
      r^n*(∫ x, f (p+r • x)*euclideanRadialWeight n x) := by
  let ρ := euclideanRadialWeight n
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hflip : (f ⋆[L,volume] euclideanRadialKernel n r) p =
      ∫ y, euclideanRadialKernel n r y*f (p-y) := by
    rw [← convolution_flip,convolution_def]
    simp [L]
  rw [hflip]
  have hscale := Measure.integral_comp_smul_of_nonneg volume
    (fun y => euclideanRadialKernel n r y*f (p-y)) r (hR := hr.le)
  have hri : r⁻¹*r = 1 := inv_mul_cancel₀ hr.ne'
  simp only [euclideanRadialKernel,smul_smul,hri,one_smul,finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul] at hscale
  have hswap : (∫ x, ρ x*f (p-r • x)) = ∫ x, f (p+r • x)*ρ x := by
    rw [← integral_neg_eq_self]
    apply integral_congr_ae
    filter_upwards with x
    have hρ : ρ (-x) = ρ x := by simp only [ρ,euclideanRadialWeight,norm_neg]
    rw [hρ,smul_neg,sub_neg_eq_add]
    ring
  rw [hswap] at hscale
  have hrn : r^n ≠ 0 := pow_ne_zero _ hr.ne'
  calc
    _ = r^n*((r^n)⁻¹*(∫ y, euclideanRadialKernel n r y*f (p-y))) := by field_simp
    _ = _ := by
      congr 1
      simpa only [euclideanRadialKernel] using hscale.symm

/-- The radial mean theorem becomes an actual local convolution identity. -/
theorem harmonic_convolution_radialKernel {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) (p : Euclidean n)
    {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r < R)
    (hh : InnerProductSpace.HarmonicOnNhd f (ball p R)) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] euclideanRadialKernel n r) p =
      (r^n*(∫ x, euclideanRadialWeight n x))*f p := by
  rw [convolution_radialKernel_eq n f p hr,harmonic_radial_mean hf hfs p hR hr hrR hh]
  ring

end RegularPointCoordinates

end

end OAI
