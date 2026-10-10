import Mathlib
import OAI.Geometry.TamingCompatibility.Currents.PlaneTest
import OAI.Geometry.TamingCompatibility.DifferentialForms.PlaneConvolution

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

lemma reflected_smooth (k : Space → ℝ) (hk : ContDiff ℝ ∞ k) (b : Space) :
    ContDiff ℝ ∞ (fun y => k (b-y)) := hk.comp (contDiff_const.sub contDiff_id)

lemma reflected_compact (k : Space → ℝ) (hc : HasCompactSupport k) (b : Space) :
    HasCompactSupport (fun y => k (b-y)) := hc.comp_homeomorph (Homeomorph.subLeft b)

lemma planeConvolution_first_variation (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (k : Space → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (b w v : Space) (hsK : tsupport (fun y => k (b-y)) ⊆ K) :
    fderiv ℝ (planeConvolution J α hs ht p K μ k) b w +
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ
        (planeCurrentTest p (fun y => k (b-y)) v
          (reflected_smooth k hk b) (reflected_compact k hc b) (hsK.trans hKT)) =
      ∫ u, (unitChartDomain J α hs ht p K).indicator
        (fun u => unitChartArea J α hs ht p u *
          fderiv ℝ k (b-unitChartBase J α hs ht p u)
            (w-skew (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u) v)) u ∂μ := by
  let S := unitChartDomain J α hs ht p K
  have hb : ContinuousOn (fun u => b-unitChartBase J α hs ht p u) S :=
    continuousOn_const.sub (unitChartBase_continuousOn J α hs ht p hKT)
  have hd : ContinuousOn (fun u => fderiv ℝ k (b-unitChartBase J α hs ht p u)) S :=
    (hk.continuous_fderiv (by simp)).comp_continuousOn hb
  have hw := planeWeighted_integrable J α hs ht p hK hKT μ
    (fun u => fderiv ℝ k (b-unitChartBase J α hs ht p u) w) (hd.clm_apply continuousOn_const)
  have hv := planeWeighted_integrable J α hs ht p hK hKT μ
    (fun u => -fderiv ℝ k (b-unitChartBase J α hs ht p u)
      (skew (unitChartFirst J α hs ht p u) (unitChartSecond J α hs ht p u) v))
    ((hd.clm_apply (unitChartSkew_continuousOn J α hs ht p v hKT)).neg)
  simp only [smul_eq_mul] at hw hv
  rw [planeConvolution_deriv J α hs ht p hK hKT μ k hk hc,
    planeCurrentTest_current J α hs ht p _ v _ _ hKT hsK μ]
  simp_rw [reflected_derivative (hk.differentiable (by simp))]
  rw [← integral_add hw hv]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  by_cases hu : u ∈ S
  · dsimp only [S] at hu
    simp only [indicator_of_mem hu,map_sub]
    ring
  · dsimp only [S] at hu
    simp only [indicator_of_notMem hu,add_zero]
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
