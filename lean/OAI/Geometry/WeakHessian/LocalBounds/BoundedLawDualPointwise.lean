import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.BoundedCost

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile228
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma lipschitz_probability_point_bound {g : X → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (μ : ProbabilityMeasure X) (x : X) {r : ℝ}
    (_hr : 0 ≤ r) (hs : ∀ᵐ z ∂(μ:Measure X),dist z x ≤ r) :
    |g x-(∫ z,g z ∂(μ:Measure X))| ≤ (L:ℝ)*r := by
  have hb : ∀ᵐ z ∂(μ:Measure X),‖g x-g z‖ ≤ (L:ℝ)*r := by
    filter_upwards [hs] with z hz
    simpa only [Real.norm_eq_abs,← Real.dist_eq] using
      (hg.dist_le_mul x z).trans (mul_le_mul_of_nonneg_left (by rwa [dist_comm]) L.coe_nonneg)
  have hi : Integrable (fun z => g x-g z) (μ:Measure X) :=
    Integrable.of_bound (continuous_const.sub hg.continuous).aestronglyMeasurable _ hb
  have hig : Integrable g (μ:Measure X) := by
    have H := (integrable_const (g x)).sub hi
    exact H.congr (Filter.Eventually.of_forall fun z => by
      change g x-(g x-g z)=g z
      ring)
  have H := norm_integral_le_of_norm_le_const hb
  rw [integral_sub (integrable_const _) hig] at H
  simpa [MeasureTheory.measureReal_def,Real.norm_eq_abs] using H

omit [SigmaFinite m] in
lemma lipschitz_dual_of_bounded_laws (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {f g : X → ℝ} {L M : ℝ≥0} (hf : LipschitzWith L f) (hg : LipschitzWith M g)
    {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ (μ₀ μ₁ : ProbabilityMeasure X) (R : ℝ≥0),
      (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0 →
      (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0 →
      ∀ C : ℝ≥0∞,C ≠ 0 → C ≠ ∞ →
      (μ₀:Measure X) ≤ C • m → (μ₁:Measure X) ≤ C • m →
      (∫ x,f x ∂(μ₁:Measure X))-(∫ x,g x ∂(μ₀:Measure X)) ≤
        A*quadraticWassersteinSq (μ₀:Measure X) (μ₁:Measure X)) :
    ∀ x y,f x-g y ≤ A*dist x y^2 := by
  intro x y
  have Hb (r : ℝ) (hr : 0 < r) : f x-g y ≤ ((L:ℝ)+(M:ℝ))*r+A*(2*r+dist x y)^2 := by
    have ht (z : X) : m (Metric.closedBall z r) ≠ ∞ := (hfin _ Metric.isBounded_closedBall).ne
    have hp (z : X) : m (Metric.closedBall z r) ≠ 0 := ne_of_gt
      ((hfull _ Metric.isOpen_ball ⟨z,Metric.mem_ball_self hr⟩).trans_le
        (measure_mono Metric.ball_subset_closedBall))
    let μ (z : X) : ProbabilityMeasure X := ⟨normalizedRestriction m (Metric.closedBall z r),
      normalizedRestriction_probability m (hp z) (ht z)⟩
    have hs (z : X) : ∀ᵐ w ∂(μ z:Measure X),dist w z ≤ r :=
      normalizedRestriction_ae_mem m Metric.isClosed_closedBall.measurableSet
    let R : ℝ≥0 := ⟨r+dist x o+dist y o,by positivity⟩
    have hS (z : X) (hz : r+dist z o ≤ R) : (μ z:Measure X) (Metric.closedBall o R)ᶜ = 0 := by
      apply ae_iff.mp
      filter_upwards [hs z] with w hw
      exact (dist_triangle w z o).trans (by linarith)
    have hSx : (μ x:Measure X) (Metric.closedBall o R)ᶜ = 0 := hS x (by
      change r+dist x o ≤ r+dist x o+dist y o
      linarith [dist_nonneg (x := y) (y := o)])
    have hSy : (μ y:Measure X) (Metric.closedBall o R)ᶜ = 0 := hS y (by
      change r+dist y o ≤ r+dist x o+dist y o
      linarith [dist_nonneg (x := x) (y := o)])
    let C : ℝ≥0∞ := (m (Metric.closedBall x r))⁻¹+(m (Metric.closedBall y r))⁻¹+1
    have hC0 : C ≠ 0 := by dsimp [C]; positivity
    have hCt : C ≠ ∞ := by
      dsimp only [C]
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.inv_ne_top.mpr (hp x),
        ENNReal.inv_ne_top.mpr (hp y)⟩,ENNReal.one_ne_top⟩
    have hdom (z : X) (hz : (m (Metric.closedBall z r))⁻¹ ≤ C) : (μ z:Measure X) ≤ C • m := by
      change (m (Metric.closedBall z r))⁻¹ • m.restrict (Metric.closedBall z r) ≤ C • m
      exact (_root_.smul_le_smul_left _ Measure.restrict_le_self).trans (by
        intro S
        simp only [Measure.smul_apply, smul_eq_mul]
        gcongr)
    have hd₁ : (μ x:Measure X) ≤ C • m := hdom x (by dsimp only [C]; exact le_add_of_le_left le_self_add)
    have hd₀ : (μ y:Measure X) ≤ C • m := hdom y (by dsimp only [C]; exact le_add_of_le_left le_add_self)
    have H := h (μ y) (μ x) R hSy hSx C hC0 hCt hd₀ hd₁
    have hc := quadraticWassersteinSq_le_of_balls (μ y) (μ x) y x hr.le hr.le (hs y) (hs x)
    have H' := H.trans (mul_le_mul_of_nonneg_left hc hA)
    have hx := lipschitz_probability_point_bound hf (μ x) x hr.le (hs x)
    have hy := lipschitz_probability_point_bound hg (μ y) y hr.le (hs y)
    rw [dist_comm y x,← two_mul r] at H'
    have hxl := (abs_le.mp hx).2
    have hyl := (abs_le.mp hy).1
    linarith
  have hlim : Tendsto (fun r : ℝ => ((L:ℝ)+(M:ℝ))*r+A*(2*r+dist x y)^2)
      (𝓝[>] 0) (𝓝 (A*dist x y^2)) := by
    have H := (by fun_prop : Continuous (fun r : ℝ => ((L:ℝ)+(M:ℝ))*r+A*(2*r+dist x y)^2)).tendsto 0
    simpa using H.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact Hb r hr
end WeakHessian

end
end InlinedFile228

end OAI
