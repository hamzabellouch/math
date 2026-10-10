import Mathlib
import OAI.Geometry.TamingCompatibility.Currents.PlaneMeasure
import OAI.Geometry.TamingCompatibility.DifferentialForms.PlaneTransverseGraph

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory PlaneVariation Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def planeConvolution (p : X) (K : Set Space)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (k : Space → ℝ) (b : Space) : ℝ :=
  ∫ y, k (b-y) ∂planeMeasure J α hs ht p K μ

lemma planeConvolution_smooth (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (k : Space → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    ContDiff ℝ ∞ (planeConvolution J α hs ht p K μ k) := by
  let := planeMeasure_finite J α hs ht p hK hKT μ
  exact finite_convolution_smooth _ k hk hc

lemma planeConvolution_deriv (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (k : Space → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) (b w : Space) :
    fderiv ℝ (planeConvolution J α hs ht p K μ k) b w =
      ∫ u, (unitChartDomain J α hs ht p K).indicator
        (fun u => unitChartArea J α hs ht p u *
          fderiv ℝ k (b-unitChartBase J α hs ht p u) w) u ∂μ := by
  let := planeMeasure_finite J α hs ht p hK hKT μ
  rw [show planeConvolution J α hs ht p K μ k = (fun b => ∫ y, k (b-y) ∂planeMeasure J α hs ht p K μ) from rfl,
    finite_convolution_deriv _ k hk hc]
  exact planeMeasure_integral J α hs ht p hK hKT μ _
    (((hk.continuous_fderiv (by simp)).comp (continuous_const.sub continuous_id)).clm_apply continuous_const)

lemma planeWeighted_integrable (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : MetricUnit (hermitianMetric J α hs ht) → W)
    (hf : ContinuousOn f (unitChartDomain J α hs ht p K)) :
    Integrable ((unitChartDomain J α hs ht p K).indicator
      (fun u => unitChartArea J α hs ht p u • f u)) μ := by
  have hS := unitChartDomain_closed J α hs ht p hK hKT
  rw [integrable_indicator_iff hS.measurableSet]
  exact ((unitChartArea_continuousOn J α hs ht p hKT).smul hf).integrableOn_compact hS.isCompact

omit [CompactSpace X] [T2Space X] in
lemma unitChartSkew_continuousOn (p : X) (v : Space) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (fun u => skew (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u) v)
      (unitChartDomain J α hs ht p K) := by
  let S := unitChartDomain J α hs ht p K
  let f := unitChartFirst J α hs ht p
  let g := unitChartSecond J α hs ht p
  have hf : ContinuousOn f S := unitChartFirst_continuousOn J α hs ht p hKT
  have hg : ContinuousOn g S := unitChartSecond_continuousOn J α hs ht p hKT
  have hi : ContinuousOn (fun u => inner ℝ (g u) v) S := hg.inner continuousOn_const
  have hj : ContinuousOn (fun u => inner ℝ (f u) v) S := hf.inner continuousOn_const
  exact (hi.smul hf).sub (hj.smul hg)

end TamingCompatibility.GeometricHilbert.Hermitian

namespace TamingCompatibility.Concentration
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma reflected_derivative {k : V → ℝ} (hk : Differentiable ℝ k) (b y w : V) :
    fderiv ℝ (fun y => k (b-y)) y w = -fderiv ℝ k (b-y) w := by
  have hh := (hk (b-y)).hasFDerivAt.comp y ((hasFDerivAt_const b y).sub (hasFDerivAt_id y))
  change HasFDerivAt (fun y => k (b-y)) _ y at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, zero_sub, neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

end TamingCompatibility.Concentration

end
end

end OAI
