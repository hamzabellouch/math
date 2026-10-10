import OAI.Geometry.RCD.Sobolev.EuclideanLaplacianDilation
import OAI.Geometry.RCD.Harmonic.EuclideanRadialAverageDerivative

namespace OAI

/-! # The radial mean identity derived from classical harmonicity -/

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped ContDiff Topology

noncomputable section
namespace RegularPointCoordinates

private theorem fderiv_affine_dilation_apply {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) (p : Euclidean n) (t : ℝ) (x v : Euclidean n) :
    fderiv ℝ (fun y => f (p+t • y)) x v = t*fderiv ℝ f (p+t • x) v := by
  have h := ((hf.differentiable (by norm_num) _).hasFDerivAt).comp x
    ((hasFDerivAt_const p x).add ((hasFDerivAt_id x).const_smul t))
  have he := congrArg (fun L : Euclidean n →L[ℝ] ℝ => L v) h.fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,add_apply,zero_apply,
    smul_apply,ContinuousLinearMap.id_apply,zero_add,map_smul,smul_eq_mul] using! he

/-- Every smooth radial weight constructed above reproduces a harmonic
function whenever its rescaled support remains inside the harmonic ball. -/
theorem harmonic_radial_mean {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) (p : Euclidean n)
    {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r < R)
    (hh : HarmonicOnNhd f (ball p R)) :
    (∫ x, f (p+r • x)*euclideanRadialWeight n x) =
      f p*(∫ x, euclideanRadialWeight n x) := by
  let A := fun t : ℝ => ∫ x, f (p+t • x)*euclideanRadialWeight n x
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_radial_average hf hfs p t).continuousAt
  have hd (t : ℝ) (ht : t ∈ Ioo 0 R) : HasDerivAt A 0 t := by
    have hcompose : ContDiff ℝ 2 (fun y => f (p+t • y)) :=
      hf.comp (contDiff_const.add (contDiff_id.const_smul t))
    have hharm : HarmonicOnNhd (fun y => f (p+t • y)) (closedBall 0 1) := by
      apply (harmonicOnNhd_affine_dilation hf hh p t).mono
      intro y hy
      change p+t • y ∈ ball p R
      rw [mem_ball,dist_eq_norm]
      have hyn : ‖y‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hy
      have he : p+t • y-p = t • y := by abel
      rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ht.1]
      exact (mul_le_mul_of_nonneg_left hyn ht.1.le).trans_lt (by simpa using ht.2)
    have hz := integral_radial_dilation_eq_zero hcompose hharm
    simp_rw [fderiv_affine_dilation_apply hf p t,mul_assoc] at hz
    rw [integral_const_mul] at hz
    have hdz : (∫ x, fderiv ℝ f (p+t • x) x*euclideanRadialWeight n x) = 0 :=
      (mul_eq_zero.mp hz).resolve_left ht.1.ne'
    simpa only [hdz] using hasDerivAt_radial_average hf hfs p t
  have hdiff : DifferentiableOn ℝ A (Ioo 0 R) := fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  have hzder : EqOn (deriv A) 0 (Ioo 0 R) := fun t ht => (hd t ht).deriv
  obtain ⟨c,hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo 0 R).isPreconnected hdiff hzder
  have hccl : EqOn A (fun _ => c) (Icc 0 R) := by
    rw [← closure_Ioo hR.ne]
    exact (show EqOn A (fun _ => c) (Ioo 0 R) from hc).closure hAc continuous_const
  have h0 := hccl (show (0:ℝ) ∈ Icc 0 R from ⟨le_rfl,hR.le⟩)
  have hr' := hccl (show r ∈ Icc 0 R from ⟨hr.le,hrR.le⟩)
  have heq : A r = A 0 := hr'.trans h0.symm
  simpa only [A,zero_smul,add_zero,integral_const_mul] using heq

end RegularPointCoordinates

end

end OAI
