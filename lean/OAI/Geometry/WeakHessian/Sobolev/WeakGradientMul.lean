import Mathlib
import OAI.Geometry.WeakHessian.Measure.InlinedFile0
import OAI.Geometry.WeakHessian.Sobolev.Minimal
import OAI.Geometry.WeakHessian.LocalBounds.MulBounded

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
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
open scoped Topology
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
namespace WeakHessian
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma weakGradient_mul_le (hfinite : FiniteOnBoundedSets m) {f η : X → ℝ}
    (hf : Sobolev m f) (hη : LocalSobolev m η) {A B : ℝ}
    (hηB : ∀ᵐ x ∂m, |η x| ≤ A) (hDB : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B) :
    ∀ᵐ x ∂m, weakGradient m (fun y => f y*η y) x ≤
      |η x| *weakGradient m f x + |f x| *weakGradient m η x :=
  (weakGradient_isMinimal (hf.mul_bounded hfinite hη hηB hDB).2.1.2).2 _
    ((weakGradient_isMinimal hf.2.1.2).1.mul_bounded (weakGradient_isMinimal hη.2).1
      hf.2.1.1 hη.1.aemeasurable hηB hDB)

lemma weakGradient_mul_error (hfinite : FiniteOnBoundedSets m) {f η ξ : X → ℝ}
    (hf : Sobolev m f) (hη : LocalSobolev m η) (hξ : LocalSobolev m ξ)
    (hθη : ∀ x, η x * ξ x = 1) (hη0 : ∀ᵐ x ∂m, 0 ≤ η x) (hξ0 : ∀ᵐ x ∂m, 0 ≤ ξ x)
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hηA : ∀ᵐ x ∂m, |η x| ≤ A) (hDη : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B)
    (hξC : ∀ᵐ x ∂m, |ξ x| ≤ C) (hDξ : ∀ᵐ x ∂m, |weakGradient m ξ x| ≤ D) :
    ∀ᵐ x ∂m, |weakGradient m (fun y => f y*η y) x - η x*weakGradient m f x| ≤
      (B + A^2*D)*|f x| := by
  have hfu := hf.mul_bounded hfinite hη hηA hDη
  have hid : (fun y => (f y * η y)*ξ y) = f := by
    funext y
    rw [mul_assoc, hθη, mul_one]
  have hu := weakGradient_mul_le hfinite hf hη hηA hDη
  have hl := weakGradient_mul_le hfinite hfu hξ hξC hDξ
  rw [hid] at hl
  filter_upwards [hu,hl,hη0,hξ0,hηA,hDη,hDξ] with x hu hl he0 hx0 heA hdη hdξ
  rw [abs_of_nonneg he0] at hu heA
  rw [abs_of_nonneg hx0,abs_mul,abs_of_nonneg he0] at hl
  have hum : weakGradient m (fun y => f y*η y) x - η x*weakGradient m f x ≤ |f x| *B := by
    have H := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hdη) (abs_nonneg (f x))
    linarith
  have hlm := mul_le_mul_of_nonneg_left hl he0
  have hmul : η x * (ξ x * weakGradient m (fun y => f y*η y) x +
      |f x| * η x * weakGradient m ξ x) =
      weakGradient m (fun y => f y*η y) x + |f x| * (η x)^2 * weakGradient m ξ x := by
    calc
      _ = (η x*ξ x)*weakGradient m (fun y => f y*η y) x +
        |f x| *(η x)^2*weakGradient m ξ x := by ring
      _ = _ := by rw [hθη,one_mul]
  rw [hmul] at hlm
  have hsq : (η x)^2 ≤ A^2 := sq_le_sq₀ he0 hA |>.mpr heA
  have hbξ : |f x| *(η x)^2*weakGradient m ξ x ≤ |f x| *A^2*D := by
    calc
      _ ≤ |f x| *(η x)^2*D := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hdξ) (by positivity)
      _ ≤ |f x| *A^2*D := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (abs_nonneg _)) hD
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hB (abs_nonneg (f x))]
  · nlinarith [mul_nonneg (mul_nonneg (sq_nonneg A) hD) (abs_nonneg (f x))]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma norm_toLp_le_mul_of_ae {f g : X → ℝ} (hf : MemLp f 2 m) (hg : MemLp g 2 m)
    {C : ℝ} (he : ∀ᵐ x ∂m, |f x| ≤ C*|g x|) :
    ‖hf.toLp f‖ ≤ C*‖hg.toLp g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [he,hf.coeFn_toLp,hg.coeFn_toLp] with x hx h1 h2
  simpa only [h1,h2,Real.norm_eq_abs] using hx

end WeakHessian

open Filter
open scoped Topology

lemma norm_sq_sub_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    (a b : E) {d : ℝ} (hd : ‖b‖ ≤ d) :
    |‖a‖^2 - ‖b‖^2| ≤ ‖a-b‖ * (2*d + ‖a-b‖) := by
  have H : |‖a‖ - ‖b‖| ≤ ‖a-b‖ := abs_norm_sub_norm_le a b
  have ha : ‖a‖ ≤ d+‖a-b‖ := by
    have hh := norm_sub_norm_le a b
    linarith
  calc
    _ = |‖a‖-‖b‖| * (‖a‖+‖b‖) := by
      rw [← abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b)), ← abs_mul]
      congr 1
      ring
    _ ≤ ‖a-b‖ * (2*d+‖a-b‖) := mul_le_mul H (by linarith)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

lemma tendsto_norm_sq_sub_norm_sq {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {a b : ℕ → E} {u : ℕ → F} {c d : ℝ}
    (he : ∀ n, ‖a n-b n‖ ≤ c*‖u n‖) (hb : ∀ n, ‖b n‖ ≤ d)
    (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => ‖a n‖^2-‖b n‖^2) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => ‖a n-b n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) he (by simpa using hu.norm.const_mul c)
  apply squeeze_zero_norm (fun n => by
    simpa only [Real.norm_eq_abs] using norm_sq_sub_norm_sq_le (a n) (b n) (hb n))
  simpa only [zero_mul] using ht.mul ((tendsto_const_nhds (x := 2*d)).add ht)

end
end InlinedFile0

end OAI
