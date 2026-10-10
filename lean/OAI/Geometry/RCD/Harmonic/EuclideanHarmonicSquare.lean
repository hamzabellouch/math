import OAI.Geometry.RCD.Metric.EuclideanGreenIdentity
import Mathlib.Analysis.Calculus.FDeriv.Pow

namespace OAI

/-! # Positivity of the Laplacian of a squared harmonic function -/

open Set Metric MeasureTheory InnerProductSpace Laplacian
open scoped ContDiff BigOperators
noncomputable section
namespace RegularPointCoordinates

theorem laplacian_square_formula {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Euclidean n) :
    (Δ (fun z => (f z)^2)) x=2*f x*(Δ f) x+
      2*∑ i : Fin n, (fderiv ℝ f x (EuclideanSpace.single i 1))^2 := by
  have hd (z v : Euclidean n) : fderiv ℝ (fun y => (f y)^2) z v=
      2*f z*fderiv ℝ f z v := by
    rw [fderiv_fun_pow 2 (hf.differentiable (by norm_num) z)]
    simp only [Nat.reduceSub,pow_one,nsmul_eq_mul,smul_apply,smul_eq_mul,Nat.cast_ofNat]
  have hdd (v : Euclidean n) :
      fderiv ℝ (fun z => fderiv ℝ (fun y => (f y)^2) z v) x v=
        2*f x*fderiv ℝ (fun z => fderiv ℝ f z v) x v+2*(fderiv ℝ f x v)^2 := by
    simp_rw [hd]
    have hdf₁ : ContDiff ℝ 1 (fun z => fderiv ℝ f z v) :=
      (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hdf : DifferentiableAt ℝ (fun z => fderiv ℝ f z v) x :=
      hdf₁.differentiable (by norm_num) x
    rw [fderiv_fun_mul ((hf.differentiable (by norm_num) x).const_mul 2) hdf,
      fderiv_const_mul (hf.differentiable (by norm_num) x)]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  rw [laplacian_eq_sum_second_directional (hf.pow 2),laplacian_eq_sum_second_directional hf]
  simp_rw [hdd]
  rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]

theorem harmonic_square_laplacian_nonneg {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Euclidean n) (hx : (Δ f) x=0) :
    0≤(Δ (fun z => (f z)^2)) x := by
  rw [laplacian_square_formula hf x,hx,mul_zero,zero_add]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end RegularPointCoordinates

end

end OAI
