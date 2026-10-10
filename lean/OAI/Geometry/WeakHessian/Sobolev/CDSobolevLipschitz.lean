import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.BoundedCost
import OAI.Geometry.WeakHessian.HeatFlow.HeatComparison
import OAI.Geometry.WeakHessian.HeatFlow.HeatProbability
import OAI.Geometry.WeakHessian.Curvature.Doubling
import OAI.Geometry.WeakHessian.Sobolev.SobolevLipschitz

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile138
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

theorem CurvatureDimension.sobolev_to_lipschitz {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hN : 1 < N) (hfull : FullSupport m)
    (hfin : FiniteOnBoundedSets m) {f D : X → ℝ} (hf : LocallyL2 m f)
    (hD : IsLocalWeakUpperGradient m f D) {L : ℝ≥0} (hbD : ∀ᵐ x ∂m,D x ≤ L) :
    ∃ f' : X → ℝ,LipschitzWith L f' ∧ f' =ᵐ[m] f := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  let : IsUnifLocDoublingMeasure m := hcd.uniform_local_doubling hN hfull hfin
  apply exists_lipschitz_of_local_ball_averages (hf.locallyIntegrable hfin)
  intro a b r hr
  have hm (x : X) : m (Metric.closedBall x r) ≠ ∞ := (hfin _ Metric.isBounded_closedBall).ne
  have hp (x : X) : m (Metric.closedBall x r) ≠ 0 := ne_of_gt
    ((hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hr⟩).trans_le (measure_mono Metric.ball_subset_closedBall))
  let u (x : X) := setDensity (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x)
  have hn (x : X) : ∀ᵐ z ∂m,0 ≤ u x z := setDensity_nonneg _ _ _
  have hmass (x : X) : ∫ z,u x z ∂m = 1 := setDensity_mass _ _ _ (hp x)
  have hbound (x : X) : ∀ᵐ z ∂m,|u x z| ≤ (m (Metric.closedBall x r)).toReal⁻¹ := setDensity_bounded _ _ _
  have hs (x : X) : ∀ᵐ z ∂m,r < dist z x → u x z = 0 := setDensity_supported _ _ _ x (Subset.refl _)
  let μ (x : X) := integrableDensityProbability (u x) (hn x) (hmass x)
  have hμ (x : X) : (μ x:Measure X) = densityMeasure m (u x) := rfl
  have hball (x : X) : ∀ᵐ z ∂(μ x:Measure X),dist z x ≤ r := densityMeasure_ae_ball (u x) x (hs x)
  let R : ℝ≥0 := ⟨2*r+dist a b,by positivity⟩
  have hsa : (μ a:Measure X) (Metric.closedBall a R)ᶜ = 0 := by
    apply ae_iff.mp
    filter_upwards [hball a] with z hz
    change dist z a ≤ 2*r+dist a b
    linarith [dist_nonneg (x := a) (y := b)]
  have hsb : (μ b:Measure X) (Metric.closedBall a R)ᶜ = 0 := by
    apply ae_iff.mp
    filter_upwards [hball b] with z hz
    change dist z a ≤ 2*r+dist a b
    have H := dist_triangle z b a
    rw [dist_comm b a] at H
    linarith
  let C : ℝ := max (m (Metric.closedBall a r)).toReal⁻¹ (m (Metric.closedBall b r)).toReal⁻¹+1
  have hC : 0 < C := by
    have hA : 0 ≤ (m (Metric.closedBall a r)).toReal⁻¹ := by positivity
    have := le_max_left (m (Metric.closedBall a r)).toReal⁻¹ (m (Metric.closedBall b r)).toReal⁻¹
    dsimp only [C]; linarith
  have hdua : (μ a:Measure X) ≤ ENNReal.ofReal C • m := by
    rw [hμ a]
    apply densityMeasure_le_const
    filter_upwards [hbound a] with z hz
    have := le_max_left (m (Metric.closedBall a r)).toReal⁻¹ (m (Metric.closedBall b r)).toReal⁻¹
    exact (le_abs_self _).trans (hz.trans (by dsimp only [C]; linarith))
  have hdub : (μ b:Measure X) ≤ ENNReal.ofReal C • m := by
    rw [hμ b]
    apply densityMeasure_le_const
    filter_upwards [hbound b] with z hz
    have := le_max_right (m (Metric.closedBall a r)).toReal⁻¹ (m (Metric.closedBall b r)).toReal⁻¹
    exact (le_abs_self _).trans (hz.trans (by dsimp only [C]; linarith))
  obtain ⟨π,hπ,htracks,hgeo,hopt,hent,hconv,hdom⟩ := hcd.exists_entropy_testPlan hN hfin (μ a) (μ b) a R hsa hsb
    (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top hdua hdub
  have he := hopt.1.interpolation_endpoints
  have hpa : ∀ᵐ γ ∂(π:Measure (Curve X)),dist (γ timeZero) a ≤ r := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeZero) (p := fun z => dist z a ≤ r) (continuous_eval_const timeZero).measurable.aemeasurable
    change ∀ᵐ z ∂interpolation (π:Measure (Curve X)) timeZero,dist z a ≤ r
    rw [he.1]
    exact hball a
  have hpb : ∀ᵐ γ ∂(π:Measure (Curve X)),dist (γ timeOne) b ≤ r := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeOne) (p := fun z => dist z b ≤ r) (continuous_eval_const timeOne).measurable.aemeasurable
    change ∀ᵐ z ∂interpolation (π:Measure (Curve X)) timeOne,dist z b ≤ r
    rw [he.2]
    exact hball b
  have hE : ∀ᵐ γ ∂(π:Measure (Curve X)),|f (γ timeOne)-f (γ timeZero)| ≤ (L:ℝ)*(2*r+dist a b) := by
    filter_upwards [hD.geodesic_endpoint_lipschitz hf.aemeasurable hbD hπ htracks hgeo,hpa,hpb] with γ hγ ha hb
    apply hγ.trans (mul_le_mul_of_nonneg_left _ L.coe_nonneg)
    have h1 := dist_triangle (γ timeZero) a (γ timeOne)
    have h2 := dist_triangle a b (γ timeOne)
    rw [dist_comm b (γ timeOne)] at h2
    linarith
  have hint0 := hf.integrable_eval hfin hπ htracks timeZero
  have hint1 := hf.integrable_eval hfin hπ htracks timeOne
  have HI : |(∫ γ,f (γ timeOne) ∂(π:Measure (Curve X)))-(∫ γ,f (γ timeZero) ∂(π:Measure (Curve X)))| ≤ (L:ℝ)*(2*r+dist a b) := by
    rw [← integral_sub hint1 hint0]
    apply abs_integral_le_integral_abs.trans
    exact (integral_mono_ae (hint1.sub hint0).abs (integrable_const _) hE).trans_eq (by simp)
  have hmap (t : Time) : (∫ γ,f (γ t) ∂(π:Measure (Curve X))) = ∫ x,f x ∂interpolation (π:Measure (Curve X)) t := by
    symm
    exact integral_map (continuous_eval_const t).measurable.aemeasurable
      (hf.aemeasurable.mono_ac (Measure.absolutelyContinuous_of_le_smul (hπ.2.1.choose_spec t))).aestronglyMeasurable
  rw [hmap timeOne,hmap timeZero,he.1,he.2,hμ a,hμ b,integral_setDensity,integral_setDensity,abs_sub_comm] at HI
  exact HI

end WeakHessian

end
end InlinedFile138

end OAI
