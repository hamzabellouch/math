import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.CircleAverage
import OAI.NumberTheory.Catalan.Energy.FirstSheetBoundaryMeasure
import OAI.NumberTheory.Catalan.Energy.FirstSheetHilbertDeterminant
import OAI.NumberTheory.Catalan.Energy.FirstSheetReproducingKernel
import OAI.NumberTheory.Catalan.Energy.RealSheetIntegralBound
import OAI.NumberTheory.Catalan.Estimates.BlaschkeUniformInterpolation

namespace OAI


noncomputable section

namespace InternalCatalan

open Complex Metric MeasureTheory
open scoped ComplexConjugate

abbrev FirstSheetBoundaryL2 := Lp ℂ 2 firstSheetBoundaryMeasure

def firstSheetBoundaryToLp : C(Circle, ℂ) →L[ℂ] FirstSheetBoundaryL2 :=
  ContinuousMap.toLp 2 firstSheetBoundaryMeasure ℂ

def firstSheetBoundaryVector (u : ℂ → ℂ)
    (hu : ContinuousOn u (closedBall (0 : ℂ) 1)) : FirstSheetBoundaryL2 :=
  firstSheetBoundaryToLp (firstSheetBoundaryFunction u hu)

theorem firstSheetBoundary_inner (f g : C(Circle, ℂ)) :
    inner ℂ (firstSheetBoundaryToLp f) (firstSheetBoundaryToLp g) =
      ∫ z : Circle, g z * conj (f z) ∂firstSheetBoundaryMeasure := by
  exact MeasureTheory.ContinuousMap.inner_toLp firstSheetBoundaryMeasure f g

theorem firstSheetBoundary_inner_function {u v : ℂ → ℂ}
    (hu : ContinuousOn u (closedBall (0 : ℂ) 1))
    (hv : ContinuousOn v (closedBall (0 : ℂ) 1)) :
    inner ℂ (firstSheetBoundaryVector u hu) (firstSheetBoundaryVector v hv) =
      Real.circleAverage (fun z => v z * conj (u z)) 0 1 := by
  rw [firstSheetBoundaryVector, firstSheetBoundaryVector, firstSheetBoundary_inner]
  exact firstSheetBoundary_integral
    (hv.mul (Complex.continuous_conj.comp_continuousOn hu))

theorem firstSheetBoundary_norm_sq (f : C(Circle, ℂ)) :
    ‖firstSheetBoundaryToLp f‖ ^ 2 =
      ∫ z : Circle, ‖f z‖ ^ 2 ∂firstSheetBoundaryMeasure := by
  have h := firstSheetBoundary_inner f f
  simp only [inner_self_eq_norm_sq_to_K, Complex.mul_conj',
    ← Complex.ofReal_pow, integral_complex_ofReal] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow]
  exact h

theorem firstSheetBoundary_norm_sq_function {u : ℂ → ℂ}
    (hu : ContinuousOn u (closedBall (0 : ℂ) 1)) :
    ‖firstSheetBoundaryVector u hu‖ ^ 2 =
      Real.circleAverage (fun z => ‖u z‖ ^ 2) 0 1 := by
  rw [firstSheetBoundaryVector, firstSheetBoundary_norm_sq]
  exact firstSheetBoundary_integral (hu.norm.pow 2)

def firstSheetKernelVector (x : ℝ) (hx : |x| < 1) : FirstSheetBoundaryL2 :=
  firstSheetBoundaryVector (firstSheetKernel x)
    (firstSheetKernel_continuousOn_closedDisk hx)

theorem firstSheetBoundary_inner_kernel {u : ℂ → ℂ}
    (hu : AnalyticOnNhd ℂ u (closedBall (0 : ℂ) 1)) {x : ℝ} (hx : |x| < 1) :
    inner ℂ (firstSheetKernelVector x hx)
      (firstSheetBoundaryVector u hu.continuousOn) = u x := by
  unfold firstSheetKernelVector
  rw [firstSheetBoundary_inner_function]
  exact circleAverage_mul_conj_firstSheetKernel hu hx

end InternalCatalan

end



noncomputable section
open scoped BigOperators ComplexConjugate
namespace InternalCatalan

def firstSheetNumerator {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ k : Fin n, a k * z ^ (k : ℕ)

def firstSheetDenominator {ι : Type*} (s : Finset ι) (x : ι → ℝ) (z : ℂ) : ℂ :=
  ∏ i ∈ s, (1 - (x i : ℂ) * z)

def firstSheetRational {ι : Type*} {n : ℕ} (s : Finset ι) (x : ι → ℝ)
    (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  firstSheetNumerator a z / firstSheetDenominator s x z

def firstSheetReverse (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) where
  toFun a k := a k.rev
  invFun a k := a k.rev
  left_inv a := by funext k; simp only [Fin.rev_rev]
  right_inv a := by funext k; simp only [Fin.rev_rev]
  map_add' a b := rfl
  map_smul' c a := rfl

def firstSheetBoundaryNormSq {ι : Type*} {n : ℕ} (s : Finset ι) (x : ι → ℝ)
    (a : Fin n → ℂ) : ℝ :=
  Real.circleAverage (fun z => ‖firstSheetRational s x a z‖ ^ 2) 0 1

theorem firstSheetReverse_involutive (n : ℕ) (a : Fin n → ℂ) :
    firstSheetReverse n (firstSheetReverse n a) = a := by
  funext k
  change a k.rev.rev = a k
  rw [Fin.rev_rev]

theorem firstSheetDenominator_ne_zero {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, |x i| < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    firstSheetDenominator s x z ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr
    (fun i hi => blaschkeFactor_denominator_ne_zero (hx i hi) hz)

theorem firstSheetDenominator_conj {ι : Type*} (s : Finset ι) (x : ι → ℝ) (z : ℂ) :
    firstSheetDenominator s x (conj z) = conj (firstSheetDenominator s x z) := by
  simp only [firstSheetDenominator, map_prod, map_sub, map_one, map_mul, Complex.conj_ofReal]

theorem firstSheetDenominator_norm_inv {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖firstSheetDenominator s x z⁻¹‖ = ‖firstSheetDenominator s x z‖ := by
  rw [Complex.inv_eq_conj hz, firstSheetDenominator_conj, Complex.norm_conj]

theorem firstSheetNumerator_reverse {n : ℕ} (a : Fin n → ℂ) {z : ℂ} (hz : z ≠ 0) :
    firstSheetNumerator (firstSheetReverse n a) z =
      z ^ (n - 1) * firstSheetNumerator a z⁻¹ := by
  have hreindex : firstSheetNumerator (firstSheetReverse n a) z =
      ∑ k : Fin n, a k * z ^ (k.rev : ℕ) := by
    change (∑ k : Fin n, a k.rev * z ^ (k : ℕ)) = _
    simpa only [Fin.revPerm_apply, Fin.rev_rev] using
      (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))
        (fun k : Fin n => a k * z ^ (k.rev : ℕ)))
  rw [hreindex, firstSheetNumerator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (k.rev : ℕ) + (k : ℕ) = n - 1 := by
    simp only [Fin.val_rev]
    omega
  calc
    a k * z ^ (k.rev : ℕ) = z ^ ((k.rev : ℕ) + (k : ℕ)) *
        (a k * (z⁻¹) ^ (k : ℕ)) := by
      rw [pow_add, inv_pow]
      field_simp [hz]
    _ = z ^ (n - 1) * (a k * (z⁻¹) ^ (k : ℕ)) := by rw [hk]

theorem firstSheetNumerator_reverse_norm {n : ℕ} (a : Fin n → ℂ)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖firstSheetNumerator (firstSheetReverse n a) z‖ = ‖firstSheetNumerator a z⁻¹‖ := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [firstSheetNumerator_reverse a hz0, norm_mul, norm_pow, hz, one_pow, one_mul]

theorem firstSheetRational_reverse_norm {ι : Type*} {n : ℕ}
    (s : Finset ι) (x : ι → ℝ) (a : Fin n → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖firstSheetRational s x (firstSheetReverse n a) z‖ =
      ‖firstSheetRational s x a z⁻¹‖ := by
  rw [firstSheetRational, firstSheetRational, norm_div, norm_div,
    firstSheetNumerator_reverse_norm a hz, firstSheetDenominator_norm_inv s x hz]

theorem firstSheetBoundaryNormSq_reverse {ι : Type*} {n : ℕ}
    (s : Finset ι) (x : ι → ℝ) (a : Fin n → ℂ) :
    firstSheetBoundaryNormSq s x (firstSheetReverse n a) = firstSheetBoundaryNormSq s x a := by
  unfold firstSheetBoundaryNormSq
  calc
    _ = Real.circleAverage (fun z => ‖firstSheetRational s x a z⁻¹‖ ^ 2) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hzn : ‖z‖ = 1 := by simpa only [abs_one, Metric.mem_sphere, dist_zero_right] using hz
      convert! congrArg (fun r : ℝ => r ^ 2) (firstSheetRational_reverse_norm s x a hzn) using 1
    _ = _ := by
      convert! (Real.circleAverage_zero_one_congr_inv
        (f := fun z : ℂ => ‖firstSheetRational s x a z‖ ^ 2)) using 1

theorem firstSheetNumerator_analyticAt {n : ℕ} (a : Fin n → ℂ) (z : ℂ) :
    AnalyticAt ℂ (firstSheetNumerator a) z := by
  unfold firstSheetNumerator
  apply Finset.analyticAt_fun_sum
  intro k _
  exact analyticAt_const.mul (analyticAt_id.pow (k : ℕ))

theorem firstSheetDenominator_analyticAt {ι : Type*} (s : Finset ι) (x : ι → ℝ) (z : ℂ) :
    AnalyticAt ℂ (firstSheetDenominator s x) z := by
  unfold firstSheetDenominator
  apply Finset.analyticAt_fun_prod
  intro i _
  exact analyticAt_const.sub (analyticAt_const.mul analyticAt_id)

theorem firstSheetRational_analyticOnNhd_closedDisk {ι : Type*} {n : ℕ}
    (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, |x i| < 1) (a : Fin n → ℂ) :
    AnalyticOnNhd ℂ (firstSheetRational s x a) (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz
  exact (firstSheetNumerator_analyticAt a z).div (firstSheetDenominator_analyticAt s x z)
    (firstSheetDenominator_ne_zero s x hx (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz))

end InternalCatalan

end



noncomputable section
open scoped BigOperators
namespace InternalCatalan

def firstSheetEvaluation {n : ℕ} (x : Fin n → ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  (Matrix.vandermonde (fun i => (x i : ℂ))).mulVecLin

theorem firstSheetEvaluation_apply {n : ℕ} (x : Fin n → ℝ) (a : Fin n → ℂ) (i : Fin n) :
    firstSheetEvaluation x a i = firstSheetNumerator a (x i : ℂ) := by
  simp only [firstSheetEvaluation, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.vandermonde_apply, firstSheetNumerator, mul_comm]

theorem firstSheetEvaluation_det_ne_zero {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) : (Matrix.vandermonde (fun i => (x i : ℂ))).det ≠ 0 := by
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro i j h
  exact hx (Complex.ofReal_injective h)

def firstSheetEvaluationEquiv {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x) :
    (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℂ (Fin n))
    (Matrix.vandermonde (fun i => (x i : ℂ)))
    (isUnit_iff_ne_zero.mpr (firstSheetEvaluation_det_ne_zero x hx))

theorem firstSheetEvaluationEquiv_apply {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (a : Fin n → ℂ) (i : Fin n) :
    firstSheetEvaluationEquiv x hx a i = firstSheetNumerator a (x i : ℂ) := by
  change (Matrix.toLin (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n))
    (Matrix.vandermonde (fun j => (x j : ℂ))) a) i = _
  rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  exact firstSheetEvaluation_apply x a i

theorem firstSheetNumerator_eq_zero_of_eval_zero {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (a : Fin n → ℂ)
    (ha : ∀ i, firstSheetNumerator a (x i : ℂ) = 0) : a = 0 := by
  apply (firstSheetEvaluationEquiv x hx).injective
  ext i
  simpa [firstSheetEvaluationEquiv_apply, firstSheetNumerator] using ha i

theorem firstSheetEvaluation_eq_denominator_mul_value {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (a : Fin n → ℂ) (i : Fin n) :
    firstSheetEvaluation x a i = firstSheetDenominator Finset.univ x (x i : ℂ) *
      firstSheetRational Finset.univ x a (x i : ℂ) := by
  have hden := firstSheetDenominator_ne_zero Finset.univ x (fun j _ => hx j)
    (show ‖(x i : ℂ)‖ ≤ 1 by simpa only [Complex.norm_real, Real.norm_eq_abs] using (hx i).le)
  rw [firstSheetEvaluation_apply, firstSheetRational]
  field_simp

def firstSheetNodeMultiplier {n : ℕ} (x : Fin n → ℝ) (h : ℂ → ℂ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun a i := h (x i : ℂ) * a i
  map_add' a b := by ext i; exact mul_add _ _ _
  map_smul' c a := by ext i; change h (x i : ℂ) * (c * a i) = c * (h (x i : ℂ) * a i); ring

def firstSheetInterpolatingMultiplier {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (h : ℂ → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  (firstSheetEvaluationEquiv x hx).symm.toLinearMap.comp
    ((firstSheetNodeMultiplier x h).comp (firstSheetEvaluationEquiv x hx).toLinearMap)

theorem firstSheetInterpolatingMultiplier_eval {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (h : ℂ → ℂ) (a : Fin n → ℂ) (i : Fin n) :
    firstSheetNumerator (firstSheetInterpolatingMultiplier x hx h a) (x i : ℂ) =
      h (x i : ℂ) * firstSheetNumerator a (x i : ℂ) := by
  rw [← firstSheetEvaluationEquiv_apply x hx]
  change firstSheetEvaluationEquiv x hx
    ((firstSheetEvaluationEquiv x hx).symm
      (firstSheetNodeMultiplier x h (firstSheetEvaluationEquiv x hx a))) i = _
  rw [LinearEquiv.apply_symm_apply]
  change h (x i : ℂ) * firstSheetEvaluationEquiv x hx a i = _
  rw [firstSheetEvaluationEquiv_apply]

def firstSheetEvaluationOperator {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (h : ℂ → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.id + (firstSheetInterpolatingMultiplier x hx h).comp (firstSheetReverse n).toLinearMap

theorem firstSheetEvaluation_cancellation {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (h : ℂ → ℂ) (a : Fin n → ℂ) (i : Fin n) :
    firstSheetEvaluation x
      (firstSheetEvaluationOperator x hx h (firstSheetReverse n a)) i =
      firstSheetNumerator (firstSheetReverse n a) (x i : ℂ) +
        h (x i : ℂ) * firstSheetNumerator a (x i : ℂ) := by
  have hnumadd (a b : Fin n → ℂ) (z : ℂ) :
      firstSheetNumerator (a + b) z = firstSheetNumerator a z + firstSheetNumerator b z := by
    simp only [firstSheetNumerator, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [firstSheetEvaluation_apply]
  change firstSheetNumerator (firstSheetReverse n a +
    firstSheetInterpolatingMultiplier x hx h (firstSheetReverse n (firstSheetReverse n a))) _ = _
  rw [firstSheetReverse_involutive, hnumadd, firstSheetInterpolatingMultiplier_eval]

end InternalCatalan

end



noncomputable section
open scoped BigOperators
namespace InternalCatalan

def firstSheetMixedEvaluationMatrix {n : ℕ} (x : Fin n → ℝ) (h : ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (fun i k => (x i : ℂ) ^ (k.rev : ℕ) + h (x i : ℂ) * (x i : ℂ) ^ (k : ℕ))

theorem firstSheetNumerator_single {n : ℕ} (k : Fin n) (z : ℂ) :
    firstSheetNumerator (Pi.single k (1 : ℂ)) z = z ^ (k : ℕ) := by
  classical
  simp [firstSheetNumerator, Pi.single_apply]

theorem firstSheetReverse_single {n : ℕ} (k : Fin n) :
    firstSheetReverse n (Pi.single k (1 : ℂ)) = Pi.single k.rev 1 := by
  classical
  ext j
  change (Pi.single k (1 : ℂ) : Fin n → ℂ) j.rev = (Pi.single k.rev (1 : ℂ) : Fin n → ℂ) j
  simp only [Pi.single_apply, eq_comm]
  by_cases hj : j = k.rev
  · subst j
    simp
  · have hk : k ≠ j.rev := by
      intro h
      apply hj
      simpa only [Fin.rev_rev] using (congrArg Fin.rev h).symm
    simp only [hj, hk, ite_false]

theorem firstSheetMixedEvaluationMatrix_eq {n : ℕ} (x : Fin n → ℝ)
    (hxi : Function.Injective x) (h : ℂ → ℂ) :
    firstSheetMixedEvaluationMatrix x h = LinearMap.toMatrix'
      ((firstSheetEvaluation x).comp
        ((firstSheetEvaluationOperator x hxi h).comp (firstSheetReverse n).toLinearMap)) := by
  ext i k
  rw [LinearMap.toMatrix'_apply]
  change _ = firstSheetEvaluation x
    (firstSheetEvaluationOperator x hxi h (firstSheetReverse n (Pi.single k 1))) i
  rw [firstSheetEvaluation_cancellation, firstSheetReverse_single, firstSheetNumerator_single,
    firstSheetNumerator_single]
  rfl

theorem firstSheetReverse_det_norm (n : ℕ) :
    ‖LinearMap.det (firstSheetReverse n).toLinearMap‖ = 1 := by
  have hc : (firstSheetReverse n).toLinearMap.comp (firstSheetReverse n).toLinearMap =
      (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
    apply LinearMap.ext
    intro a
    exact firstSheetReverse_involutive n a
  have hd := congrArg LinearMap.det hc
  rw [LinearMap.det_comp, LinearMap.det_id] at hd
  have hn := congrArg norm hd
  rw [norm_mul, norm_one] at hn
  nlinarith [norm_nonneg (LinearMap.det (firstSheetReverse n).toLinearMap)]

theorem firstSheetEvaluation_det {n : ℕ} (x : Fin n → ℝ) :
    LinearMap.det (firstSheetEvaluation x) =
      (Matrix.vandermonde (fun i => (x i : ℂ))).det := by
  unfold firstSheetEvaluation
  rw [← Matrix.toLin'_apply']
  exact LinearMap.det_toLin' _

theorem firstSheetMixedEvaluationMatrix_det {n : ℕ} (x : Fin n → ℝ)
    (hxi : Function.Injective x) (h : ℂ → ℂ) :
    (firstSheetMixedEvaluationMatrix x h).det =
      (Matrix.vandermonde (fun i => (x i : ℂ))).det *
        LinearMap.det (firstSheetEvaluationOperator x hxi h) *
          LinearMap.det (firstSheetReverse n).toLinearMap := by
  rw [firstSheetMixedEvaluationMatrix_eq x hxi]
  rw [LinearMap.det_toMatrix', LinearMap.det_comp, LinearMap.det_comp, firstSheetEvaluation_det]
  ring

theorem firstSheetMixedEvaluationMatrix_norm_div {n : ℕ} (x : Fin n → ℝ)
    (hxi : Function.Injective x) (h : ℂ → ℂ) :
    ‖(firstSheetMixedEvaluationMatrix x h).det‖ /
      ‖(Matrix.vandermonde (fun i => (x i : ℂ))).det‖ =
        ‖LinearMap.det (firstSheetEvaluationOperator x hxi h)‖ := by
  rw [firstSheetMixedEvaluationMatrix_det x hxi, norm_mul, norm_mul, firstSheetReverse_det_norm, mul_one]
  have hv := norm_ne_zero_iff.mpr (firstSheetEvaluation_det_ne_zero x hxi)
  exact mul_div_cancel_left₀ _ hv

end InternalCatalan

end



noncomputable section
open Polynomial
open scoped BigOperators
namespace InternalCatalan

def firstSheetKernelNumerator {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℂ[X] :=
  ∏ j ∈ Finset.univ.erase i, (1 - C (x j : ℂ) * X)

def firstSheetKernelCoefficients {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : Fin n → ℂ :=
  fun k => (firstSheetKernelNumerator x i).coeff (k : ℕ)

theorem firstSheetNumerator_coefficients {n : ℕ} (p : ℂ[X]) (hp : p.natDegree < n) (z : ℂ) :
    firstSheetNumerator (fun k : Fin n => p.coeff (k : ℕ)) z = p.eval z := by
  change (∑ k : Fin n, p.coeff (k : ℕ) * z ^ (k : ℕ)) = _
  calc
    _ = ∑ k ∈ Finset.range n, p.coeff k * z ^ k :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ => p.coeff k * z ^ k) n
    _ = p.eval z := by
      rw [Polynomial.eval_eq_sum, Polynomial.sum]
      symm
      apply Finset.sum_subset
      · intro k hk
        exact Finset.mem_range.mpr ((Polynomial.le_natDegree_of_mem_supp _ hk).trans_lt hp)
      · intro k _ hk
        have hcoeff : p.coeff k = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hk
        rw [hcoeff, zero_mul]

theorem firstSheetKernelNumerator_natDegree_lt {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (firstSheetKernelNumerator x i).natDegree < n := by
  have hfactor (j : Fin n) : (1 - C (x j : ℂ) * (X : ℂ[X])).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  calc
    (firstSheetKernelNumerator x i).natDegree ≤
        ∑ j ∈ Finset.univ.erase i, (1 - C (x j : ℂ) * (X : ℂ[X])).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 := Finset.sum_le_sum (fun j _ => hfactor j)
    _ = n - 1 := by simp
    _ < n := by have hi := i.isLt; omega

theorem firstSheetKernelCoefficients_numerator {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (z : ℂ) :
    firstSheetNumerator (firstSheetKernelCoefficients x i) z =
      ∏ j ∈ Finset.univ.erase i, (1 - (x j : ℂ) * z) := by
  change firstSheetNumerator (fun k : Fin n => (firstSheetKernelNumerator x i).coeff (k : ℕ)) z = _
  rw [firstSheetNumerator_coefficients _ (firstSheetKernelNumerator_natDegree_lt x i)]
  simp only [firstSheetKernelNumerator, eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X]

theorem firstSheetRational_kernelCoefficients {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (i : Fin n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    firstSheetRational Finset.univ x (firstSheetKernelCoefficients x i) z =
      firstSheetKernel (x i) z := by
  have hden := firstSheetDenominator_ne_zero Finset.univ x (fun j _ => hx j) hz
  have hi := blaschkeFactor_denominator_ne_zero (hx i) hz
  have hp : (1 - (x i : ℂ) * z) *
      (∏ j ∈ Finset.univ.erase i, (1 - (x j : ℂ) * z)) = firstSheetDenominator Finset.univ x z :=
    Finset.mul_prod_erase Finset.univ (fun j => 1 - (x j : ℂ) * z) (Finset.mem_univ i)
  rw [firstSheetRational, firstSheetKernelCoefficients_numerator, firstSheetKernel]
  apply (div_eq_iff hden).mpr
  rw [← hp, ← mul_assoc, inv_mul_cancel₀ hi, one_mul]

end InternalCatalan

end



noncomputable section
open Complex MeasureTheory
open scoped BigOperators
namespace InternalCatalan

def firstSheetRationalBoundaryMap {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1) :
    (Fin n → ℂ) →ₗ[ℂ] C(Circle, ℂ) where
  toFun a := firstSheetBoundaryFunction (firstSheetRational Finset.univ x a)
    (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun i _ => hx i) a).continuousOn
  map_add' a b := by
    ext z
    change firstSheetRational Finset.univ x (a + b) (z : ℂ) =
      firstSheetRational Finset.univ x a (z : ℂ) + firstSheetRational Finset.univ x b (z : ℂ)
    simp only [firstSheetRational, firstSheetNumerator, Pi.add_apply, add_mul,
      Finset.sum_add_distrib, add_div]
  map_smul' c a := by
    ext z
    change firstSheetRational Finset.univ x (c • a) (z : ℂ) =
      c * firstSheetRational Finset.univ x a (z : ℂ)
    simp only [firstSheetRational, firstSheetNumerator, Pi.smul_apply, smul_eq_mul,
      mul_assoc, ← Finset.mul_sum, mul_div_assoc]

def firstSheetRationalEmbedding {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1) :
    (Fin n → ℂ) →ₗ[ℂ] FirstSheetBoundaryL2 :=
  firstSheetBoundaryToLp.toLinearMap.comp (firstSheetRationalBoundaryMap x hx)

theorem firstSheetRationalEmbedding_apply {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (a : Fin n → ℂ) :
    firstSheetRationalEmbedding x hx a =
      firstSheetBoundaryVector (firstSheetRational Finset.univ x a)
        (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun i _ => hx i) a).continuousOn := rfl

theorem firstSheetRationalEmbedding_inner_kernel {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (a : Fin n → ℂ) (i : Fin n) :
    inner ℂ (firstSheetKernelVector (x i) (hx i)) (firstSheetRationalEmbedding x hx a) =
      firstSheetRational Finset.univ x a (x i : ℂ) := by
  rw [firstSheetRationalEmbedding_apply]
  exact firstSheetBoundary_inner_kernel
    (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun j _ => hx j) a) (hx i)

theorem firstSheetRationalEmbedding_injective {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) :
    Function.Injective (firstSheetRationalEmbedding x hx) := by
  intro a b hab
  apply (firstSheetEvaluationEquiv x hxi).injective
  ext i
  have hip := congrArg (fun v => inner ℂ (firstSheetKernelVector (x i) (hx i)) v) hab
  rw [firstSheetRationalEmbedding_inner_kernel, firstSheetRationalEmbedding_inner_kernel] at hip
  have heval := congrArg (fun w : ℂ => firstSheetDenominator Finset.univ x (x i : ℂ) * w) hip
  rw [← firstSheetEvaluation_eq_denominator_mul_value x hx a i,
    ← firstSheetEvaluation_eq_denominator_mul_value x hx b i] at heval
  simpa only [firstSheetEvaluationEquiv_apply, firstSheetEvaluation_apply] using heval

def firstSheetSpace {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1) :
    Submodule ℂ FirstSheetBoundaryL2 := (firstSheetRationalEmbedding x hx).range

instance firstSheetSpace_finiteDimensional {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1) :
    FiniteDimensional ℂ (firstSheetSpace x hx) := by
  unfold firstSheetSpace
  infer_instance

theorem firstSheetKernelVector_mem_space {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (i : Fin n) :
    firstSheetKernelVector (x i) (hx i) ∈ firstSheetSpace x hx := by
  refine ⟨firstSheetKernelCoefficients x i, ?_⟩
  rw [firstSheetRationalEmbedding_apply]
  unfold firstSheetKernelVector firstSheetBoundaryVector
  apply congrArg firstSheetBoundaryToLp
  ext z
  exact firstSheetRational_kernelCoefficients x hx i (by simp only [Circle.norm_coe, le_refl])

theorem firstSheetRationalEmbedding_norm_sq {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (a : Fin n → ℂ) :
    ‖firstSheetRationalEmbedding x hx a‖ ^ 2 = firstSheetBoundaryNormSq Finset.univ x a := by
  rw [firstSheetRationalEmbedding_apply]
  exact firstSheetBoundary_norm_sq_function _

theorem firstSheetRationalEmbedding_reverse_norm {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (a : Fin n → ℂ) :
    ‖firstSheetRationalEmbedding x hx (firstSheetReverse n a)‖ =
      ‖firstSheetRationalEmbedding x hx a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [firstSheetRationalEmbedding_norm_sq, firstSheetRationalEmbedding_norm_sq,
    firstSheetBoundaryNormSq_reverse]

def firstSheetProjection {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1) :
    FirstSheetBoundaryL2 →L[ℂ] FirstSheetBoundaryL2 :=
  (firstSheetSpace x hx).starProjection

theorem firstSheetProjection_norm_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (u : FirstSheetBoundaryL2) :
    ‖firstSheetProjection x hx u‖ ≤ ‖u‖ :=
  (firstSheetSpace x hx).norm_starProjection_apply_le u

theorem firstSheetProjection_inner_kernel {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (u : FirstSheetBoundaryL2) (i : Fin n) :
    inner ℂ (firstSheetKernelVector (x i) (hx i)) (firstSheetProjection x hx u) =
      inner ℂ (firstSheetKernelVector (x i) (hx i)) u := by
  have h := inner_eq_zero_symm.mp ((firstSheetSpace x hx).starProjection_inner_eq_zero
    u (firstSheetKernelVector (x i) (hx i)) (firstSheetKernelVector_mem_space x hx i))
  rw [inner_sub_right, sub_eq_zero] at h
  exact h.symm

end InternalCatalan

end



noncomputable section
open Complex Metric
open scoped BigOperators
namespace InternalCatalan

theorem firstSheetBoundary_mul_norm_le {h u : ℂ → ℂ}
    (hh : ContinuousOn h (closedBall (0 : ℂ) 1))
    (hu : ContinuousOn u (closedBall (0 : ℂ) 1)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) 1, ‖h z‖ ≤ K) :
    ‖firstSheetBoundaryVector (fun z => h z * u z) (hh.mul hu)‖ ≤
      K * ‖firstSheetBoundaryVector u hu‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
  rw [mul_pow, firstSheetBoundary_norm_sq_function, firstSheetBoundary_norm_sq_function]
  have hcu := hu.norm.pow 2
  have hch := (hh.mul hu).norm.pow 2
  have hcr : ContinuousOn (fun z => K ^ 2 * ‖u z‖ ^ 2) (closedBall (0 : ℂ) 1) :=
    continuousOn_const.mul hcu
  calc
    Real.circleAverage (fun z => ‖h z * u z‖ ^ 2) 0 1 ≤
        Real.circleAverage (fun z => K ^ 2 * ‖u z‖ ^ 2) 0 1 := by
      apply Real.circleAverage_mono
        (ContinuousOn.circleIntegrable (by norm_num) (hch.mono sphere_subset_closedBall))
        (ContinuousOn.circleIntegrable (by norm_num) (hcr.mono sphere_subset_closedBall))
      intro z hz
      change ‖h z * u z‖ ^ 2 ≤ K ^ 2 * ‖u z‖ ^ 2
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hbound z (sphere_subset_closedBall (by simpa using hz))) 2)
        (sq_nonneg _)
    _ = K ^ 2 * Real.circleAverage (fun z => ‖u z‖ ^ 2) 0 1 := by
      simpa only [smul_eq_mul] using (Real.circleAverage_fun_smul
        (a := K ^ 2) (f := fun z : ℂ => ‖u z‖ ^ 2) (c := 0) (R := 1))

theorem firstSheetProjection_mul_eq {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (closedBall (0 : ℂ) 1)) (a : Fin n → ℂ) :
    firstSheetProjection x hx
      (firstSheetBoundaryVector (fun z => h z * firstSheetRational Finset.univ x a z)
        (hh.mul (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun i _ => hx i) a)).continuousOn) =
      firstSheetRationalEmbedding x hx (firstSheetInterpolatingMultiplier x hxi h a) := by
  let u : FirstSheetBoundaryL2 := firstSheetBoundaryVector
    (fun z => h z * firstSheetRational Finset.univ x a z)
    (hh.mul (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun i _ => hx i) a)).continuousOn
  have hmem : firstSheetProjection x hx u ∈ firstSheetSpace x hx :=
    (firstSheetSpace x hx).starProjection_apply_mem u
  obtain ⟨b, hb⟩ := hmem
  have hba : b = firstSheetInterpolatingMultiplier x hxi h a := by
    apply (firstSheetEvaluationEquiv x hxi).injective
    ext i
    rw [firstSheetEvaluationEquiv_apply, firstSheetEvaluationEquiv_apply,
      firstSheetInterpolatingMultiplier_eval]
    have hip := firstSheetProjection_inner_kernel x hx u i
    rw [← hb, firstSheetRationalEmbedding_inner_kernel] at hip
    have hrepro := firstSheetBoundary_inner_kernel
      (hh.mul (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun j _ => hx j) a)) (hx i)
    change inner ℂ (firstSheetKernelVector (x i) (hx i)) u =
      h (x i : ℂ) * firstSheetRational Finset.univ x a (x i : ℂ) at hrepro
    rw [hrepro] at hip
    have hden := firstSheetDenominator_ne_zero Finset.univ x (fun j _ => hx j)
      (show ‖(x i : ℂ)‖ ≤ 1 by simpa only [Complex.norm_real, Real.norm_eq_abs] using (hx i).le)
    unfold firstSheetRational at hip
    field_simp [hden] at hip
    exact hip
  rw [hba] at hb
  exact hb.symm

theorem firstSheetInterpolatingMultiplier_norm_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (closedBall (0 : ℂ) 1)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) 1, ‖h z‖ ≤ K) (a : Fin n → ℂ) :
    ‖firstSheetRationalEmbedding x hx (firstSheetInterpolatingMultiplier x hxi h a)‖ ≤
      K * ‖firstSheetRationalEmbedding x hx a‖ := by
  rw [← firstSheetProjection_mul_eq x hx hxi h hh a]
  refine (firstSheetProjection_norm_le x hx _).trans ?_
  rw [firstSheetRationalEmbedding_apply]
  exact firstSheetBoundary_mul_norm_le hh.continuousOn
    (firstSheetRational_analyticOnNhd_closedDisk Finset.univ x (fun i _ => hx i) a).continuousOn hK hbound

theorem firstSheetEvaluationOperator_norm_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (closedBall (0 : ℂ) 1)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) 1, ‖h z‖ ≤ K) (a : Fin n → ℂ) :
    ‖firstSheetRationalEmbedding x hx (firstSheetEvaluationOperator x hxi h a)‖ ≤
      (1 + K) * ‖firstSheetRationalEmbedding x hx a‖ := by
  change ‖firstSheetRationalEmbedding x hx
    (a + firstSheetInterpolatingMultiplier x hxi h (firstSheetReverse n a))‖ ≤ _
  rw [map_add]
  calc
    _ ≤ ‖firstSheetRationalEmbedding x hx a‖ +
        ‖firstSheetRationalEmbedding x hx (firstSheetInterpolatingMultiplier x hxi h (firstSheetReverse n a))‖ :=
      norm_add_le _ _
    _ ≤ ‖firstSheetRationalEmbedding x hx a‖ +
        K * ‖firstSheetRationalEmbedding x hx (firstSheetReverse n a)‖ :=
      add_le_add (le_refl _) (firstSheetInterpolatingMultiplier_norm_le x hx hxi h hh hK hbound _)
    _ = (1 + K) * ‖firstSheetRationalEmbedding x hx a‖ := by
      rw [firstSheetRationalEmbedding_reverse_norm]
      ring

end InternalCatalan

end



noncomputable section
namespace InternalCatalan

def firstSheetSpaceEquiv {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1)
    (hxi : Function.Injective x) : (Fin n → ℂ) ≃ₗ[ℂ] firstSheetSpace x hx :=
  LinearEquiv.ofInjective (firstSheetRationalEmbedding x hx)
    (firstSheetRationalEmbedding_injective x hx hxi)

theorem firstSheetSpaceEquiv_coe {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1)
    (hxi : Function.Injective x) (a : Fin n → ℂ) :
    (firstSheetSpaceEquiv x hx hxi a : FirstSheetBoundaryL2) = firstSheetRationalEmbedding x hx a := rfl

theorem firstSheetSpace_finrank {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1)
    (hxi : Function.Injective x) : Module.finrank ℂ (firstSheetSpace x hx) = n := by
  rw [← (firstSheetSpaceEquiv x hx hxi).finrank_eq]
  simp

def firstSheetSpaceOperator {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1)
    (hxi : Function.Injective x) (h : ℂ → ℂ) :
    firstSheetSpace x hx →ₗ[ℂ] firstSheetSpace x hx :=
  (firstSheetSpaceEquiv x hx hxi).toLinearMap.comp
    ((firstSheetEvaluationOperator x hxi h).comp (firstSheetSpaceEquiv x hx hxi).symm.toLinearMap)

theorem firstSheetSpaceOperator_norm_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (Metric.closedBall (0 : ℂ) 1)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖h z‖ ≤ K) (u : firstSheetSpace x hx) :
    ‖firstSheetSpaceOperator x hx hxi h u‖ ≤ (1 + K) * ‖u‖ := by
  obtain ⟨a, rfl⟩ := (firstSheetSpaceEquiv x hx hxi).surjective u
  change ‖firstSheetSpaceEquiv x hx hxi
    (firstSheetEvaluationOperator x hxi h
      ((firstSheetSpaceEquiv x hx hxi).symm (firstSheetSpaceEquiv x hx hxi a)))‖ ≤ _
  rw [LinearEquiv.symm_apply_apply]
  change ‖firstSheetRationalEmbedding x hx (firstSheetEvaluationOperator x hxi h a)‖ ≤
    (1 + K) * ‖firstSheetRationalEmbedding x hx a‖
  exact firstSheetEvaluationOperator_norm_le x hx hxi h hh hK hbound a

theorem firstSheetSpaceOperator_det {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1)
    (hxi : Function.Injective x) (h : ℂ → ℂ) :
    LinearMap.det (firstSheetSpaceOperator x hx hxi h) =
      LinearMap.det (firstSheetEvaluationOperator x hxi h) :=
  LinearMap.det_conj _ (firstSheetSpaceEquiv x hx hxi)

end InternalCatalan




open scoped BigOperators
namespace InternalCatalan

theorem firstSheetMixedEvaluationMatrix_norm_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (Metric.closedBall (0 : ℂ) 1)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖h z‖ ≤ K) :
    ‖(firstSheetMixedEvaluationMatrix x h).det‖ ≤
      (1 + K) ^ n * ‖(Matrix.vandermonde (fun i => (x i : ℂ))).det‖ := by
  have hdet := firstSheet_det_norm_le_pow (firstSheetSpaceOperator x hx hxi h)
    (firstSheetSpaceOperator_norm_le x hx hxi h hh hK hbound)
  rw [firstSheetSpaceOperator_det, firstSheetSpace_finrank x hx hxi] at hdet
  rw [firstSheetMixedEvaluationMatrix_det x hxi, norm_mul, norm_mul,
    firstSheetReverse_det_norm, mul_one]
  calc
    _ ≤ ‖(Matrix.vandermonde (fun i => (x i : ℂ))).det‖ * (1 + K) ^ n :=
      mul_le_mul_of_nonneg_left hdet (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem firstSheet_uniform_mixed_determinant_bound {n D : ℕ} (x : Fin n → ℝ)
    (hn : 48 ≤ n) (hDpos : 0 < D) (hDn : D ≤ n)
    (hx0 : ∀ i, x i ≠ 0) (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x)
    (hweight : (∑ i : Fin n, blaschkeWeight (x i)) ≤ (D : ℝ)) :
    ‖(Matrix.of (fun i k : Fin n =>
      (x i : ℂ) ^ (k.rev : ℕ) +
        (if x i < 0 then (x i : ℂ) ^ D else -5 * (x i : ℂ) ^ D) *
          (x i : ℂ) ^ (k : ℕ))).det‖ ≤
      (1 + 10 * Real.exp 12 * (n : ℝ)) ^ n *
        ‖(Matrix.vandermonde (fun i => (x i : ℂ))).det‖ := by
  obtain ⟨h, hh, heval, hbound⟩ := real_uniform_interpolation_actual Finset.univ x D n hn
    hDpos hDn (by simp) (fun i _ => hx0 i) (fun i _ => hx i) hweight
  have hm : firstSheetMixedEvaluationMatrix x h = Matrix.of (fun i k : Fin n =>
      (x i : ℂ) ^ (k.rev : ℕ) +
        (if x i < 0 then (x i : ℂ) ^ D else -5 * (x i : ℂ) ^ D) *
          (x i : ℂ) ^ (k : ℕ)) := by
    ext i k
    simp only [firstSheetMixedEvaluationMatrix, Matrix.of_apply, heval i (Finset.mem_univ i)]
  rw [← hm]
  exact firstSheetMixedEvaluationMatrix_norm_le x hx hxi h hh (by positivity) hbound

end InternalCatalan

end



noncomputable section
open scoped BigOperators
namespace InternalCatalan

theorem firstSheet_norm_ofReal_det {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    ‖(M.map Complex.ofReal).det‖ = |M.det| := by
  calc
    _ = ‖(M.det : ℂ)‖ := congrArg norm (Complex.ofRealHom.map_det M).symm
    _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs]

theorem firstSheet_uniform_real_mixed_determinant_bound {m D : ℕ} (x : Fin m → ℝ)
    (hm : 48 ≤ m) (hDpos : 0 < D) (hDm : D ≤ m)
    (hx0 : ∀ i, x i ≠ 0) (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x)
    (hweight : (∑ i : Fin m, blaschkeWeight (x i)) ≤ (D : ℝ)) :
    |(Matrix.of (fun r i : Fin m => x i ^ (r.rev : ℕ) +
      (if x i < 0 then x i ^ D else -5 * x i ^ D) * x i ^ (r : ℕ))).det| ≤
      (1 + 10 * Real.exp 12 * (m : ℝ)) ^ m * |(Matrix.vandermonde x).det| := by
  let M : Matrix (Fin m) (Fin m) ℝ := Matrix.of (fun r i => x i ^ (r.rev : ℕ) +
    (if x i < 0 then x i ^ D else -5 * x i ^ D) * x i ^ (r : ℕ))
  have hmap : Matrix.of (fun i k : Fin m =>
      (x i : ℂ) ^ (k.rev : ℕ) +
        (if x i < 0 then (x i : ℂ) ^ D else -5 * (x i : ℂ) ^ D) * (x i : ℂ) ^ (k : ℕ)) =
      (M.map Complex.ofReal).transpose := by
    ext i k
    by_cases hi : x i < 0 <;> simp [M, hi]
  have hv : Matrix.vandermonde (fun i => (x i : ℂ)) =
      (Matrix.vandermonde x).map Complex.ofReal := by
    ext i k
    simp [Matrix.vandermonde_apply]
  have hb := firstSheet_uniform_mixed_determinant_bound x hm hDpos hDm hx0 hx hxi hweight
  rw [hmap, Matrix.det_transpose, hv, firstSheet_norm_ofReal_det, firstSheet_norm_ofReal_det] at hb
  exact hb

theorem firstSheet_laurent_vandermonde_weight {m : ℕ} (g : ℕ) (x : Fin m → ℝ)
    (hx0 : ∀ i, x i ≠ 0) :
    (∏ i : Fin m, |x i ^ ((g : ℤ) - ((m - 1 : ℕ) : ℤ))|) *
        |(Matrix.vandermonde x).det| =
      |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| *
        ∏ i : Fin m, |x i| ^ g := by
  have hp (i : Fin m) : |x i ^ ((g : ℤ) - ((m - 1 : ℕ) : ℤ))| =
      |x i| ^ g / |x i| ^ (m - 1) := by
    rw [abs_zpow, zpow_sub₀ (abs_ne_zero.mpr (hx0 i)), zpow_natCast, zpow_natCast]
  simp only [hp, Finset.prod_div_distrib]
  rw [Matrix.det_vandermonde, abs_vandermonde_inv x hx0]
  ring

end InternalCatalan

end



noncomputable section
open Set
open scoped BigOperators
namespace InternalCatalan

theorem realSheetDeterminant_first_sheet_bound {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x)
    (hcase : (∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) ≤
      ((n N - 1 - 2 * g N : ℕ) : ℝ)) :
    |realSheetDeterminant N x| ≤
      (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| *
          ∏ i : Fin (n N), |x i| ^ g N := by
  have hn : 48 ≤ n N := by unfold n; omega
  have hDpos : 0 < n N - 1 - 2 * g N := by unfold n g; omega
  have hDn : n N - 1 - 2 * g N ≤ n N := by omega
  have hxabs : ∀ i, |x i| < 1 := fun i => abs_lt.mpr (hx i)
  have hweight : (∑ i : Fin (n N), blaschkeWeight (x i)) ≤
      ((n N - 1 - 2 * g N : ℕ) : ℝ) := by
    simpa only [blaschkeWeight] using hcase
  have hmixed : |(realFirstSheetMixedMatrix N x).det| ≤
      (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N * |(Matrix.vandermonde x).det| :=
    firstSheet_uniform_real_mixed_determinant_bound x hn hDpos hDn hx0 hxabs hxi hweight
  have hprod : 0 ≤ ∏ i : Fin (n N), |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) :=
    Finset.prod_nonneg (fun i _ => zpow_nonneg (abs_nonneg (x i)) _)
  have hw : (∏ i : Fin (n N), |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
      |(Matrix.vandermonde x).det| =
      |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| *
        ∏ i : Fin (n N), |x i| ^ g N := by
    simpa only [abs_zpow] using firstSheet_laurent_vandermonde_weight (g N) x hx0
  calc
    |realSheetDeterminant N x| ≤
        (∏ i : Fin (n N), |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
          |(realFirstSheetMixedMatrix N x).det| :=
      realSheetDeterminant_abs_le_firstSheet_mixed hN x hx0
    _ ≤ (∏ i : Fin (n N), |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
        ((1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N * |(Matrix.vandermonde x).det|) :=
      mul_le_mul_of_nonneg_left hmixed hprod
    _ = (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N *
        ((∏ i : Fin (n N), |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
          |(Matrix.vandermonde x).det|) := by ring
    _ = _ := by rw [hw]; ring

end InternalCatalan

end



noncomputable section
open Set
open scoped BigOperators

namespace InternalCatalan

theorem abs_sheetRealIntegrand_le_majorantTwo {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hcase : (∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) ≤
      ((n N - 1 - 2 * g N : ℕ) : ℝ)) :
    |sheetRealIntegrand N x s| ≤
      (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N * realEnergyMajorantTwo N x s := by
  rw [abs_sheetRealIntegrand_eq N x s hx hs]
  calc
    _ ≤ ((1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N *
        |∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, ((x j)⁻¹ - (x i)⁻¹)| *
        (∏ i : Fin (n N), |x i| ^ g N)) * realPrincipalIntegrand N x s :=
      mul_le_mul_of_nonneg_right (realSheetDeterminant_first_sheet_bound hN x hx hx0 hxi hcase)
        (realPrincipalIntegrand_nonneg N x s hx hs)
    _ = _ := by unfold realEnergyMajorantTwo; ring

end InternalCatalan

end



noncomputable section
open Set
open scoped BigOperators

namespace InternalCatalan

theorem abs_determinant_le_of_two_majorant_bounds {N : ℕ} (hN : 0 < N)
    {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hbound₁ : ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (((n N - 1 - 2 * g N : ℕ) : ℝ) <
        ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) →
      realEnergyMajorantOne N x s ≤ M₁)
    (hbound₂ : ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      ((∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) ≤
        ((n N - 1 - 2 * g N : ℕ) : ℝ)) →
      realEnergyMajorantTwo N x s ≤ M₂) :
    |determinant N| ≤
      ((2 : ℝ) ^ n N *
        max ((1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N)
          ((3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2)) /
        (((n N).factorial : ℝ) ^ 2)) * max M₁ M₂ := by
  let K₁ : ℝ := (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N
  let K₂ : ℝ := (3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2)
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (Nat.cast_nonneg (n N)) _)
  have hK : 0 ≤ max K₁ K₂ := hK₁.trans (le_max_left _ _)
  have hM : 0 ≤ max M₁ M₂ := hM₁.trans (le_max_left _ _)
  have hsheet : ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      |sheetRealIntegrand N x s| ≤ max K₁ K₂ * max M₁ M₂ := by
    intro x s hx hs hx0 hxi hsi
    by_cases hcase : (∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) ≤
        ((n N - 1 - 2 * g N : ℕ) : ℝ)
    · calc
        _ ≤ K₁ * realEnergyMajorantTwo N x s :=
          abs_sheetRealIntegrand_le_majorantTwo hN x s hx hx0 hxi hs hcase
        _ ≤ K₁ * M₂ :=
          mul_le_mul_of_nonneg_left (hbound₂ x s hx hs hx0 hxi hsi hcase) hK₁
        _ ≤ max K₁ K₂ * max M₁ M₂ :=
          mul_le_mul (le_max_left _ _) (le_max_right _ _) hM₂ hK
    · calc
        _ ≤ K₂ * realEnergyMajorantOne N x s :=
          abs_sheetRealIntegrand_le_majorantOne hN x s hx hx0 hs
        _ ≤ K₂ * M₁ :=
          mul_le_mul_of_nonneg_left (hbound₁ x s hx hs hx0 hxi hsi (lt_of_not_ge hcase)) hK₂
        _ ≤ max K₁ K₂ * max M₁ M₂ :=
          mul_le_mul (le_max_right _ _) (le_max_left _ _) hM₁ hK
  have hi := abs_determinant_le_of_sheetRealIntegrand_bound hN (mul_nonneg hK hM) hsheet
  apply hi.trans_eq
  dsimp [K₁, K₂]
  ring

end InternalCatalan

end

end OAI
