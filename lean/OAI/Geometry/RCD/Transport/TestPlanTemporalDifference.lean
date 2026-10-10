import OAI.Geometry.RCD.Sobolev.MovingLinearDifference
import OAI.Analysis.RCDHeat.SobolevTestPlan

namespace OAI

/-! # The temporal part of a moving test-plan pairing

Strong L2 differentiation and continuity of compressed evaluations suffice;
no pointwise derivative along the diagonal of time and paths is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates

def lpMeanCLM {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν] :
    Lp ℝ 2 ν →L[ℝ] ℝ :=
  innerSL ℝ ((memLp_const (1:ℝ)).toLp (fun _ => 1))

theorem lpMeanCLM_apply {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] (f : Lp ℝ 2 ν) :
    lpMeanCLM ν f = ∫ y, f y ∂ν := by
  change inner ℝ ((memLp_const (1:ℝ)).toLp (fun _ => 1)) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_const (1:ℝ) (μ := ν) (p := 2)).coeFn_toLp] with y hy
  simp only [Real.inner_apply,hy,one_mul]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

def testPlanMeanCLM (μ : Measure X) (π : Measure C(Time,X)) [IsFiniteMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) (t : ℝ) :
    Lp ℝ 2 μ →L[ℝ] ℝ :=
  (lpMeanCLM π).comp (testPlanPullback μ π hC hcomp (Set.projIcc 0 1 zero_le_one t))

theorem testPlanMeanCLM_apply (μ : Measure X) (π : Measure C(Time,X)) [IsFiniteMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) (t : ℝ) (f : Lp ℝ 2 μ) :
    testPlanMeanCLM μ π hC hcomp t f = ∫ γ : C(Time,X), f (geodesicExtension γ t) ∂π := by
  rw [testPlanMeanCLM,ContinuousLinearMap.comp_apply,lpMeanCLM_apply]
  exact integral_congr_ae (compressionPullback_ae μ π _
    (measurable_path_eval (Set.projIcc 0 1 zero_le_one t)) hC (hcomp _) f)

variable [ProperSpace X] (μ : Measure X) [μ.Regular]

theorem testPlanMeanCLM_jointly_continuous (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hLength : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π) :
    Continuous (fun q : Lp ℝ 2 μ × ℝ => testPlanMeanCLM μ π hC hcomp q.2 q.1) := by
  have hp : Continuous (fun q : Lp ℝ 2 μ × ℝ =>
      (q.1, (Set.projIcc 0 1 zero_le_one q.2 : Time))) :=
    continuous_fst.prodMk ((LipschitzWith.projIcc zero_le_one).continuous.comp continuous_snd)
  have hbase : Continuous (fun q : Lp ℝ 2 μ × Time =>
      testPlanPullback μ π hC hcomp q.2 q.1) :=
    testPlanPullback_jointly_continuous μ π hgeo hC hcomp hLength
  have he : Continuous (fun q : Lp ℝ 2 μ × ℝ =>
      testPlanPullback μ π hC hcomp (Set.projIcc 0 1 zero_le_one q.2) q.1) := by
    change Continuous ((fun q : Lp ℝ 2 μ × Time => testPlanPullback μ π hC hcomp q.2 q.1) ∘
      (fun q : Lp ℝ 2 μ × ℝ => (q.1,(Set.projIcc 0 1 zero_le_one q.2 : Time))))
    exact hbase.comp hp
  change Continuous (fun q : Lp ℝ 2 μ × ℝ => lpMeanCLM π
    (testPlanPullback μ π hC hcomp (Set.projIcc 0 1 zero_le_one q.2) q.1))
  exact (lpMeanCLM π).continuous.comp he

theorem testPlan_temporal_difference_tendsto (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hLength : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (u : ℝ → Lp ℝ 2 μ) {s : ℝ} {D : Lp ℝ 2 μ} (hu : HasDerivAt u D s) :
    Tendsto (fun t => ((∫ γ : C(Time,X), u t (geodesicExtension γ t) ∂π) -
        (∫ γ : C(Time,X), u s (geodesicExtension γ t) ∂π))/(t-s))
      (𝓝[≠] s) (𝓝 (∫ γ : C(Time,X), D (geodesicExtension γ s) ∂π)) := by
  have hh := moving_linear_difference_tendsto (testPlanMeanCLM μ π hC hcomp) u
    (testPlanMeanCLM_jointly_continuous μ π hgeo hC hcomp hLength).continuousAt hu
  simpa only [testPlanMeanCLM_apply,smul_eq_mul,div_eq_mul_inv,mul_comm] using hh

end RegularPointCoordinates

end

end OAI
