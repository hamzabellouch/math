import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ExcessRelocation
import OAI.Geometry.WeakHessian.Transport.CdEntropyPlanBounded
import OAI.Geometry.WeakHessian.Entropy.CenteredMulLogDeriv

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
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma optimalTimeLaw_supported_ball {μ₀ μ₁ μ : ProbabilityMeasure X} {t : Time}
    (hμ : μ ∈ optimalTimeLaws μ₀ μ₁ t) (o : X) (R : ℝ)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0) :
    (μ:Measure X) (Metric.closedBall o (3*R))ᶜ = 0 := by
  obtain ⟨π,hgeo,hopt,hμ⟩ := hμ
  subst μ
  exact geodesic_plan_supported_ball (π:Measure (Curve X)) hgeo o R
    (by simpa only [hopt.1.interpolation_endpoints.1] using hb₀)
    (by simpa only [hopt.1.interpolation_endpoints.2] using hb₁) t

theorem CurvatureDimension.exists_entropy_improving_sharp_midpoint
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    (μref : ProbabilityMeasure X) (href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf)
    (hEref : FiniteEntropy m (μref:Measure X)) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧
      FiniteEntropy m (μ:Measure X) ∧ entropyReal m (μ:Measure X) ≤ entropyReal m (μref:Measure X) := by
  let a : ℝ≥0∞ := ((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos
    (ENNReal.mul_pos_iff.mpr ⟨by norm_num,midpointTauLower_pos _ _ _⟩)
    (ENNReal.mul_ne_top (by simp) (midpointTauLower_ne_top hN))).ne'
  have hat : a ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero
    (mul_ne_zero (by norm_num) (midpointTauLower_pos _ _ _).ne')
    (ENNReal.mul_ne_top (by simp) (midpointTauLower_ne_top hN))
  let B := C/a
  have hB : B ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hC,hat⟩
  have hBt : B ≠ ∞ := ENNReal.div_ne_top hCt ha0
  let Q := Metric.closedBall o (3*(R:ℝ))
  have hQ : MeasurableSet Q := Metric.isClosed_closedBall.measurableSet
  let : IsFiniteMeasure (m.restrict Q) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin Q Metric.isBounded_closedBall⟩
  have hsref : ∀ᵐ x ∂(μref:Measure X), x ∈ Q :=
    ae_iff.mpr (optimalTimeLaw_supported_ball href o R hb₀ hb₁)
  have hErefQ := (finiteEntropy_restrict_reference_iff hQ hsref).mpr hEref
  let κ := (m.restrict Q).withDensity (fun x => min ((μref:Measure X).rnDeriv (m.restrict Q) x) B)
  have hκcap : κ ≤ B • m.restrict Q := by
    rw [← withDensity_const]
    exact withDensity_mono (ae_of_all _ fun x => min_le_right _ _)
  have hκref : κ ≤ (μref:Measure X) := by
    rw [← Measure.withDensity_rnDeriv_eq (μref:Measure X) (m.restrict Q) hErefQ.1]
    exact withDensity_mono (ae_of_all _ fun x => min_le_left _ _)
  obtain ⟨μ,hμ,hdμ,hκμ⟩ := hcd.exists_sharp_midpoint_above_lower hN hfin o R hb₀ hb₁
    hC hCt hd₀ hd₁ κ hκcap μref href hκref
  obtain ⟨hEμQ,hent⟩ := entropyReal_le_of_density_capping (μref:Measure X) (μ:Measure X)
    hErefQ hB hBt hdμ hκμ
  have hsμ : ∀ᵐ x ∂(μ:Measure X), x ∈ Q :=
    ae_iff.mpr (optimalTimeLaw_supported_ball hμ o R hb₀ hb₁)
  have hEμ := (finiteEntropy_restrict_reference_iff hQ hsμ).mp hEμQ
  refine ⟨μ,hμ,hdμ,hEμ,?_⟩
  rwa [entropyReal_restrict_reference hQ hEμ.1 hsμ,
    entropyReal_restrict_reference hQ hEref.1 hsref] at hent

lemma endpointCost_eq_ofReal_integral [SecondCountableTopology X]
    (π : ProbabilityMeasure (Curve X)) {μ₀ μ₁ : ProbabilityMeasure X} (o : X) (R : ℝ≥0)
    (hg : ∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ)
    (he : IsCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0) :
    QuadraticTransportCost (endpointCoupling (π:Measure (Curve X))) =
      ENNReal.ofReal (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂(π:Measure (Curve X))) := by
  have hs := optimalPlan_supported_tube π hg he hb₀ hb₁
  rw [endpointCost_eq_clipped_integral (π:Measure (Curve X)) hs]
  congr 1
  apply integral_congr_ae
  exact (ae_iff.mpr hs).mono fun γ hγ => clippedEndpointCost_eq hγ

lemma optimal_cost_integral_eq [SecondCountableTopology X]
    (π η : ProbabilityMeasure (Curve X)) {μ₀ μ₁ : ProbabilityMeasure X} (o : X) (R : ℝ≥0)
    (hgπ : ∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ)
    (hgη : ∀ᵐ γ ∂(η:Measure (Curve X)), IsGeodesic γ)
    (hπ : IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁)
    (hη : IsOptimalCoupling (endpointCoupling (η:Measure (Curve X))) μ₀ μ₁)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0) :
    (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂(π:Measure (Curve X))) =
      (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂(η:Measure (Curve X))) := by
  apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)).mp
  rw [← endpointCost_eq_ofReal_integral π o R hgπ hπ.1 hb₀ hb₁,
    ← endpointCost_eq_ofReal_integral η o R hgη hη.1 hb₀ hb₁]
  exact le_antisymm (hπ.2 _ hη.1) (hη.2 _ hπ.1)

theorem CurvatureDimension.exists_entropy_bounded_midpoint
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) (μ₀ μ₁ : ProbabilityMeasure X)
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    (hE₀ : FiniteEntropy m (μ₀:Measure X)) (hE₁ : FiniteEntropy m (μ₁:Measure X)) :
    ∃ π : ProbabilityMeasure (Curve X),
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁ ∧
      interpolation (π:Measure (Curve X)) timeHalf ≤
        (C/((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N) • m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧
      FiniteEntropy m (interpolation (π:Measure (Curve X)) timeHalf) ∧
      entropyReal m (interpolation (π:Measure (Curve X)) timeHalf) ≤
        (entropyReal m (μ₀:Measure X)+entropyReal m (μ₁:Measure X))/2 -
          K/8*(∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂(π:Measure (Curve X))) := by
  obtain ⟨π,hp,hg,ho,hE⟩ := cd_entropy_plan_bounded hN hcd hfin hE₀ hE₁ o R.2
    (ae_iff.mpr hb₀) (ae_iff.mpr hb₁)
  let := hp
  let πp : ProbabilityMeasure (Curve X) := ⟨π,hp⟩
  let μref : ProbabilityMeasure X := πp.map (fun γ => γ timeHalf)
  have href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf := ⟨πp,hg,ho,rfl⟩
  obtain ⟨μ,hμ,hdμ,hEμ,hentμ⟩ := hcd.exists_entropy_improving_sharp_midpoint
    hN hfin o R hb₀ hb₁ hC hCt hd₀ hd₁ μref href (hE timeHalf).1
  obtain ⟨η,hgη,hoη,hμeq⟩ := hμ
  have hcost := optimal_cost_integral_eq πp η o R hg hgη ho hoη hb₀ hb₁
  have hbound := hentμ.trans (hE timeHalf).2
  rw [hμeq] at hdμ hEμ hbound
  refine ⟨η,hgη,hoη,hdμ,hEμ,?_⟩
  change entropyReal m (interpolation (η:Measure (Curve X)) timeHalf) ≤ _ at hbound
  change (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π) = _ at hcost
  rw [hcost] at hbound
  convert hbound using 1
  dsimp only [timeHalf]
  ring

end WeakHessian

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

end
end InlinedFile0

end OAI
