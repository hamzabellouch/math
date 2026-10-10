import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.BoundedMulLp
import OAI.Geometry.WeakHessian.Sobolev.WeakGradientMul

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma norm_toLp_sq_eq_integral {f : X → ℝ} (hf : MemLp f 2 m) :
    ‖hf.toLp f‖^2 = ∫ x, (f x)^2 ∂m := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hx]

lemma tendsto_gradient_mul_error (hfinite : FiniteOnBoundedSets m)
    {fs : ℕ → X → ℝ} (hs : ∀ n, Sobolev m (fs n)) {η ξ : X → ℝ}
    (hη : LocalSobolev m η) (hξ : LocalSobolev m ξ)
    (hei : ∀ x, η x * ξ x = 1) (hη0 : ∀ᵐ x ∂m, 0 ≤ η x) (hξ0 : ∀ᵐ x ∂m, 0 ≤ ξ x)
    {A B C D R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hηA : ∀ᵐ x ∂m, |η x| ≤ A) (hDη : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B)
    (hξC : ∀ᵐ x ∂m, |ξ x| ≤ C) (hDξ : ∀ᵐ x ∂m, |weakGradient m ξ x| ≤ D)
    (hR : ∀ n, ‖(hs n).2.2.toLp (weakGradient m (fs n))‖ ≤ R)
    (ht : Tendsto (fun n => (hs n).1.toLp (fs n)) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ x, (weakGradient m (fun y => fs n y*η y) x)^2 ∂m) -
      ∫ x, (weakGradient m (fs n) x * η x)^2 ∂m) atTop (𝓝 0) := by
  let hu (n : ℕ) := hs n |>.mul_bounded hfinite hη hηA hDη
  let hv (n : ℕ) := memLp_mul_bounded (hs n).2.2 hη.1.aestronglyMeasurable hηA
  let a (n : ℕ) := (hu n).2.2.toLp (weakGradient m (fun y => fs n y*η y))
  let b (n : ℕ) := (hv n).toLp (fun x => weakGradient m (fs n) x * η x)
  have he (n : ℕ) : ‖a n-b n‖ ≤ (B+A^2*D)*‖(hs n).1.toLp (fs n)‖ := by
    apply norm_toLp_le_mul_of_ae ((hu n).2.2.sub (hv n)) (hs n).1
    have H := weakGradient_mul_error hfinite (hs n) hη hξ hei hη0 hξ0 hA hB hD hηA hDη hξC hDξ
    simpa only [Pi.sub_apply, mul_comm (η _) (weakGradient m (fs n) _)] using H
  have hb (n : ℕ) : ‖b n‖ ≤ A*R := by
    apply le_trans (norm_toLp_le_mul_of_ae (hv n) (hs n).2.2 ?_) (mul_le_mul_of_nonneg_left (hR n) hA)
    filter_upwards [hηA] with x hx
    simpa only [abs_mul, mul_comm] using mul_le_mul_of_nonneg_left hx (abs_nonneg (weakGradient m (fs n) x))
  have H := tendsto_norm_sq_sub_norm_sq he hb ht
  simpa only [a,b,norm_toLp_sq_eq_integral] using H
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
