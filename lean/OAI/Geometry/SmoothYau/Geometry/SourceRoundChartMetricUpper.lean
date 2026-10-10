import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ContinuousCompactSmoothJets

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter Manifold
open scoped Topology ContDiff InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma roundChart_metric_conformal (p : E) (L : F →ₗᵢ[ℝ] E)
    (hp : inner ℝ p p=1) (hL : ∀ v, inner ℝ p (L v)=0) (x v w : F) :
    inner ℝ (fderiv ℝ (roundChart p L) x v) (fderiv ℝ (roundChart p L) x w) =
      (16/(‖x‖^2+4)^2)*inner ℝ v w := by
  have hL' : ∀ v, inner ℝ (L v) p=0 := fun v => (real_inner_comm _ _).trans (hL v)
  rw [roundChart_directional,roundChart_directional,stereoAux_directional,stereoAux_directional]
  simp only [inner_sub_left,inner_sub_right,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,inner_neg_left,inner_neg_right,
    L.norm_map,L.inner_map_map,hp,hL,hL',real_inner_self_eq_norm_sq,starRingEnd_apply,star_trivial]
  have hpos : ‖x‖^2+4 ≠ 0 := by positivity
  rw [real_inner_comm v x,real_inner_comm w x]
  field_simp
  ring

lemma roundChart_pole_pairing (p : E) (L : F →ₗᵢ[ℝ] E)
    (hp : inner ℝ p p=1) (hL : ∀ v, inner ℝ p (L v)=0) (x : F) :
    1+inner ℝ p (roundChart p L x)=8/(‖x‖^2+4) := by
  simp only [roundChart,stereoInvFunAux,inner_smul_right,inner_add_right,
    inner_neg_right,hp,hL,L.norm_map,mul_zero,zero_add]
  have hpos : ‖x‖^2+4 ≠ 0 := by positivity
  field_simp
  ring


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter Manifold Metric
open scoped Topology ContDiff InnerProductSpace

lemma source_round_chart_metric_upper
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {y : Euclidean 3}
    (hy : y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10))
    (v : Euclidean 3) :
    selfMetricFlat (sphereChartMetric g₀ sourcePole) y v v ≤ (1/2:ℝ)*‖v‖^2 := by
  let q := (chartAt (Euclidean 3) sourcePole).symm y
  have hp : inner ℝ (sourcePole : Euclidean 4) (sourcePole : Euclidean 4)=1 :=
    source_axes_orthonormal.1
  have hr := (mem_sphericalCoverage_iff sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole (by norm_num : (3/10:ℝ)<1) y).mp hy
  have hrs := sphericalRadius_sq sourceAxisOne sourceAxisTwo q
  have hr0 := sphericalRadius_nonneg sourceAxisOne sourceAxisTwo q
  have hx : |inner ℝ sourceAxisOne (q : Euclidean 4)| ≤ 3/10 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤3/10)).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (inner ℝ sourceAxisTwo (q : Euclidean 4))]
  have hh := roundChart_pole_pairing (sourcePole : Euclidean 4)
    (sphereFrame sourcePole) hp (sphereFrame_orthogonal sourcePole) y
  rw [←congrFun (sphere_chart_symm sourcePole) y] at hh
  change 1+inner ℝ sourceAxisOne (q : Euclidean 4)=8/(‖y‖^2+4) at hh
  have hden : ‖y‖^2+4 ≠ 0 := by positivity
  have he : 16/(‖y‖^2+4)^2 = (1+inner ℝ sourceAxisOne (q:Euclidean 4))^2/4 := by
    rw [hh]
    field_simp
    ring
  rw [selfMetricFlat_apply,sphereChartMetric_round g₀ hg₀,
    roundChart_metric_conformal _ _ hp (sphereFrame_orthogonal sourcePole),he,
    real_inner_self_eq_norm_sq]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hx' := abs_le.mp hx
  nlinarith

theorem spherical_coordinate_upper_neighborhood
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀) :
    IsSmoothNeighborhood g₀ {g | ∀ y ∈
      sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2} := by
  have hK := sphericalCoverage_compact sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole (by norm_num : (3/10:ℝ)<1)
  apply IsSmoothNeighborhood.mono g₀ (sphere_metric_first_jet_neighborhood g₀ sourcePole hK
    (by norm_num : (0:ℝ)<1/2))
  intro g hg y hy v
  have hdiff := (hg y hy).1
  have hb := source_round_chart_metric_upper g₀ hg₀ hy v
  have he : |selfMetricFlat (sphereChartMetric g sourcePole) y v v-
      selfMetricFlat (sphereChartMetric g₀ sourcePole) y v v| ≤ (1/2:ℝ)*‖v‖^2 := by
    calc
      _ = ‖(selfMetricFlat (sphereChartMetric g sourcePole) y-
        selfMetricFlat (sphereChartMetric g₀ sourcePole) y) v v‖ := by simp
      _ ≤ ‖selfMetricFlat (sphereChartMetric g sourcePole) y-
        selfMetricFlat (sphereChartMetric g₀ sourcePole) y‖*‖v‖*‖v‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hdiff.le (sq_nonneg ‖v‖)]
  have hh := (abs_le.mp he).2
  linarith



end YauCounterexamples
end

end OAI
