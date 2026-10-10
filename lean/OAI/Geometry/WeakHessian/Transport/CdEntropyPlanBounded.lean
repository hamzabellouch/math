import Mathlib
import OAI.Geometry.WeakHessian.Entropy.CdEntropyBoundFinite

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
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology

namespace WeakHessian
open MeasureTheory InformationTheory
open scoped ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma cd_entropy_plan_bounded {m μ₀ μ₁ : Measure X}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfinite : FiniteOnBoundedSets m)
    (hE₀ : FiniteEntropy m μ₀) (hE₁ : FiniteEntropy m μ₁)
    (o : X) {R : ℝ} (hR : 0 ≤ R)
    (hs₀ : ∀ᵐ x ∂μ₀, dist x o ≤ R) (hs₁ : ∀ᵐ x ∂μ₁, dist x o ≤ R) :
    ∃ π : Measure (Curve X), IsProbabilityMeasure π ∧ (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling π) μ₀ μ₁ ∧
      ∀ t : Time, FiniteEntropy m (interpolation π t) ∧
        entropyReal m (interpolation π t) ≤ (1-(t:ℝ))*entropyReal m μ₀+(t:ℝ)*entropyReal m μ₁ -
          K/2*(t:ℝ)*(1-(t:ℝ))*(∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π) := by
  let : SigmaFinite m := sigmaFinite_of_finiteOnBoundedSets m hfinite o
  obtain ⟨π,hπ,hgeo,hopt,hτ⟩ := hcd μ₀ μ₁ inferInstance inferInstance
    (hasSecondMoment_of_ae_dist_le o R hs₀) (hasSecondMoment_of_ae_dist_le o R hs₁) hE₀.1 hE₁.1
  let : IsProbabilityMeasure π := hπ
  obtain ⟨hm₀,hm₁⟩ := hopt.1.interpolation_endpoints
  have hγ₀ : ∀ᵐ γ ∂π, dist (γ timeZero) o ≤ R := by
    have H : ∀ᵐ x ∂interpolation π timeZero, dist x o ≤ R := by simpa only [hm₀] using hs₀
    exact ae_of_ae_map (continuous_eval_const timeZero).measurable.aemeasurable H
  have hγ₁ : ∀ᵐ γ ∂π, dist (γ timeOne) o ≤ R := by
    have H : ∀ᵐ x ∂interpolation π timeOne, dist x o ≤ R := by simpa only [hm₁] using hs₁
    exact ae_of_ae_map (continuous_eval_const timeOne).measurable.aemeasurable H
  have hlen : ∀ᵐ γ ∂π, dist (γ timeZero) (γ timeOne) ≤ 2*R := by
    filter_upwards [hγ₀,hγ₁] with γ h0 h1
    have H := dist_triangle (γ timeZero) o (γ timeOne)
    rw [dist_comm o] at H
    linarith
  have htracks : ∀ᵐ γ ∂π, ∀ t : Time, γ t ∈ Metric.closedBall o (3*R+1) := by
    filter_upwards [hγ₀,hlen,hgeo] with γ h0 hL hg
    intro t
    have H := dist_triangle (γ t) (γ timeZero) o
    rw [hg,show (timeZero:ℝ)=0 from rfl,sub_zero,abs_of_nonneg t.2.1] at H
    have HH := mul_le_mul_of_nonneg_right t.2.2 (dist_nonneg (x := γ timeZero) (y := γ timeOne))
    simp only [one_mul] at HH
    change dist (γ t) o ≤ 3*R+1
    linarith
  have hs0Q : ∀ᵐ x ∂μ₀, x ∈ Metric.closedBall o (3*R+1) := hs₀.mono fun x hx => by
    change dist x o ≤ 3*R+1
    linarith
  have hs1Q : ∀ᵐ x ∂μ₁, x ∈ Metric.closedBall o (3*R+1) := hs₁.mono fun x hx => by
    change dist x o ≤ 3*R+1
    linarith
  let d : ℕ → ℝ := fun n => N+(n:ℝ)
  have hd : ∀ n, 1 < d n := fun n => by dsimp [d]; exact hN.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hdlim : Tendsto (fun n => 1/d n) atTop (𝓝 0) := by
    simp only [one_div]
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_atTop_add_const_left _ N tendsto_natCast_atTop_atTop
  refine ⟨π,hπ,hgeo,hopt,fun t => ?_⟩
  let : IsProbabilityMeasure (interpolation π t) := interpolation_probability π t
  have hst : ∀ᵐ x ∂interpolation π t, x ∈ Metric.closedBall o (3*R+1) := by
    exact (ae_map_iff (continuous_eval_const t).measurable.aemeasurable Metric.isClosed_closedBall.measurableSet).mpr
      (htracks.mono fun γ hγ => hγ t)
  apply cd_entropy_bound_on_finite_region
    (continuous_eval_const timeZero).measurable (continuous_eval_const timeOne).measurable
    hm₀ hm₁ hE₀ hE₁ Metric.isClosed_closedBall.measurableSet
    (hfinite _ Metric.isBounded_closedBall) hs0Q hs1Q hst
    ((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).measurable
    (Eventually.of_forall fun γ => dist_nonneg) (sq_nonneg (2*R))
    (hlen.mono fun γ hγ => pow_le_pow_left₀ dist_nonneg hγ 2) t.2.1 t.2.2 hd hdlim
  exact fun n => hτ (d n) (by dsimp [d]; exact le_add_of_nonneg_right (Nat.cast_nonneg _)) t
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
