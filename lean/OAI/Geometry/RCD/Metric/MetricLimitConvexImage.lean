import OAI.Geometry.RCD.Metric.PointedMetricLimitSegments
import Mathlib.Analysis.Convex.StrictConvexBetween

namespace OAI

/-! # The locally isometric coordinate image of a metric-limit ball is convex -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [ProperSpace Y]

theorem metric_limit_convex_image (hgeo : IsGeodesicSpace X)
    {q : Y} (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hr : ∀ k, 0<r k) (hε0 : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (ε k) (V k))
    {n : ℕ} (F : Y → Euclidean n) (hF : Continuous F)
    (hiso : ∀ y z, dist y q<1/16 → dist z q<1/16 → dist (F y) (F z)=dist y z) :
    IsCompact (F '' closedBall q (1/256)) ∧ Convex ℝ (F '' closedBall q (1/256)) := by
  refine ⟨(isCompact_closedBall q (1/256:ℝ)).image hF,?_⟩
  rintro _ ⟨y,hy,rfl⟩ _ ⟨z,hz,rfl⟩ s t hs ht hst
  have hy' : dist y q<1/128 := (show dist y q≤1/256 from hy).trans_lt (by norm_num)
  have hz' : dist z q<1/128 := (show dist z q≤1/256 from hz).trans_lt (by norm_num)
  let τ : Time := ⟨t,ht,by linarith⟩
  obtain ⟨b,hb,hby,hbz⟩ := pointed_metric_limit_segment hgeo p r ε V hr hε0 hV hy' hz' τ
  have hb' : dist b q<1/16 := hb.trans_lt (by norm_num)
  have hy'' : dist y q<1/16 := hy'.trans (by norm_num)
  have hz'' : dist z q<1/16 := hz'.trans (by norm_num)
  have he : F b=AffineMap.lineMap (F y) (F z) t := by
    apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
    · rw [hiso y b hy'' hb',hiso y z hy'' hz'']
      exact hby
    · rw [hiso b z hb' hz'',hiso y z hy'' hz'']
      exact hbz
  have hf : F b=s • F y+t • F z := by
    rw [he,AffineMap.lineMap_apply]
    have heq : s=1-t := by linarith
    rw [heq]
    simp only [vsub_eq_sub,vadd_eq_add]
    module
  have hFy : F y∈closedBall (F q) (1/256) := by
    change dist (F y) (F q)≤1/256
    rw [hiso y q hy'' (by simp)]
    exact hy
  have hFz : F z∈closedBall (F q) (1/256) := by
    change dist (F z) (F q)≤1/256
    rw [hiso z q hz'' (by simp)]
    exact hz
  have hFb : F b∈closedBall (F q) (1/256) := by
    rw [hf]
    exact (convex_closedBall (F q) (1/256:ℝ)) hFy hFz hs ht hst
  have hbin : b∈closedBall q (1/256) := by
    change dist b q≤1/256
    rwa [← hiso b q hb' (by simp)]
  exact ⟨b,hbin,hf⟩

end RegularPointCoordinates

end

end OAI
