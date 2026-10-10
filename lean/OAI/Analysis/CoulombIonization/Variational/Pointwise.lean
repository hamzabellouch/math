import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma square_partition_derivative (p : J → E → ℝ)
    (hp : ∀ j, Differentiable ℝ (p j)) (h : ∀ x, ∑ j, p j x ^ 2 = 1)
    (x v : E) : ∑ j, p j x * lineDeriv ℝ (p j) x v = 0 := by
  have he : (fun x => ∑ j, p j x ^ 2) = fun _ => (1 : ℝ) := funext h
  have hd := congrArg (fun f : E → ℝ => fderiv ℝ f x v) he
  change fderiv ℝ (fun y => ∑ j, p j y ^ 2) x v = fderiv ℝ (fun _ : E => (1 : ℝ)) x v at hd
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun j y => p j y ^ 2) (fun j _ => (hp j x).pow 2), fderiv_const_apply] at hd
  simp only [sum_apply, fderiv_fun_pow 2 (hp _ x), smul_apply,
    smul_eq_mul, Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat, zero_apply] at hd
  have hs : (∑ j, 2 * p j x * fderiv ℝ (p j) x v) =
      2 * ∑ j, p j x * lineDeriv ℝ (p j) x v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [(hp j x).lineDeriv_eq_fderiv]
    ring
  rw [hs] at hd
  linarith

lemma complex_norm_square_expansion (p d : ℝ) (a b : ℂ) :
    ‖(p : ℂ) * a + (d : ℂ) * b‖ ^ 2 = p ^ 2 * ‖a‖ ^ 2 +
      d ^ 2 * ‖b‖ ^ 2 + 2 * (p * d) * (a.re * b.re + a.im * b.im) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma finite_complex_ims (p d : J → ℝ) (hp : ∑ j, p j ^ 2 = 1)
    (hd : ∑ j, p j * d j = 0) (a b : ℂ) :
    (∑ j, ‖(p j : ℂ) * a + (d j : ℂ) * b‖ ^ 2) =
      ‖a‖ ^ 2 + (∑ j, d j ^ 2) * ‖b‖ ^ 2 := by
  simp_rw [complex_norm_square_expansion]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hp, hd]
  ring

lemma finite_complex_partition (p : J → ℝ) (hp : ∑ j, p j ^ 2 = 1) (z : ℂ) :
    ∑ j, ‖(p j : ℂ) * z‖ ^ 2 = ‖z‖ ^ 2 := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    ← Finset.sum_mul, hp, one_mul]

end CoulombAtom

end

end OAI
