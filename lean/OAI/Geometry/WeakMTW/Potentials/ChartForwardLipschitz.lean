import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.BundleMinimizerCompactness
import OAI.Geometry.WeakMTW.Variations.CostSplitting

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem chart_forward_local_lipschitz (x : M) :
     ∃ r : ℝ, ∃ C : ℝ≥0, 0 < r ∧ Metric.ball x r ⊆ (chartAt (Model n) x).source ∧
       LipschitzOnWith C (chartAt (Model n) x) (Metric.ball x r) := by
   let : IsContinuousRiemannianBundle (Model n) (fun y : M => TangentSpace (model n) y) := by
     obtain ⟨g,hg,he⟩ := (IsContMDiffRiemannianBundle.exists_contMDiff (IB := model n) (n := ∞)
       (F := Model n) (E := fun y : M => TangentSpace (model n) y))
     exact ⟨g,hg.continuous,he⟩
   obtain ⟨C,hC,hCb⟩ := eventually_norm_mfderiv_extChartAt_lt (model n) x
   let c := chartAt (Model n) x
   have hCb' : ∀ᶠ y in 𝓝 x,
       ContinuousLinearMap.opNorm (mfderiv (model n) (model n) c y) < C := by
     exact hCb
   obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp (inter_mem
     (c.open_source.mem_nhds (mem_chart_source (Model n) x)) hCb')
   refine ⟨δ/4,⟨C,hC.le⟩,by positivity,
     fun y hy => (hδb (Metric.ball_subset_ball (by linarith) hy)).1,?_⟩
   apply LipschitzOnWith.of_dist_le_mul
   intro y hy z hz
   obtain ⟨v,hv,hn⟩ := exists_minimizing_vector (n := n) y z
   let q : TangentBundle (model n) M := ⟨y,v⟩
   have hqm : q ∈ totalMinimizingSet := by change dist y (exp y v) = ‖v‖; rw [hv,hn]
   have hdz : dist y z < δ/2 := by
     have h := dist_triangle y x z
     rw [dist_comm x z] at h
     change dist y x < δ/4 at hy
     change dist z x < δ/4 at hz
     linarith
   have hpath (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : geodesic q s ∈ Metric.ball x δ := by
     have hd := minimizing_shortened_dist hqm (s := 0) (t := s) (le_refl 0) hs.1 hs.2
     simp only [zero_smul,exp_zero,sub_zero,exp_mul_eq_geodesic] at hd
     have hD : dist y (geodesic q s) ≤ dist y z := by rw [hd,hn]; exact mul_le_of_le_one_left dist_nonneg hs.2
     change dist (geodesic q s) x < δ
     have h := dist_triangle (geodesic q s) y x
     rw [dist_comm (geodesic q s) y] at h
     change dist y x < δ/4 at hy
     linarith
   have hdiff (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : DifferentiableAt ℝ (c ∘ geodesic q) s := by
     exact mdifferentiableAt_iff_differentiableAt.mp
       ((((contMDiffOn_chart (n := ∞)).contMDiffAt
         (c.open_source.mem_nhds (hδb (hpath s hs)).1)).mdifferentiableAt (by simp)).comp
         s ((geodesic_smooth q).mdifferentiable (by simp) s))
   have hbound (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖deriv (c ∘ geodesic q) s‖ ≤ C*‖v‖ := by
     have hsrc := (hδb (hpath s hs)).1
     rw [curveState_chart_deriv' x ((geodesic_smooth q).mdifferentiable (by simp) s) hsrc]
     have hch := congrArg (fun p : TangentBundle (model n) (Model n) => p.2)
       (tangentMap_chart (p := (⟨x,0⟩ : TangentBundle (model n) M))
         (q := geodesicFlow s q) hsrc)
     change mfderiv (model n) (model n) c (geodesic q s) (geodesicFlow s q).2 =
       (stateChart x (geodesicFlow s q)).2 at hch
     change ‖(stateChart x (geodesicFlow s q)).2‖ ≤ C*‖v‖
     rw [←hch]
     exact ((mfderiv (model n) (model n) c (geodesic q s)).le_opNorm _).trans
       ((mul_le_mul_of_nonneg_right (hδb (hpath s hs)).2.le
         (norm_nonneg (geodesicFlow s q).2)).trans_eq
           (congrArg (C * ·) (geodesicFlow_norm s q)))
   have hd := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc (0:ℝ) 1)
     (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
     (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
   have hq1 : geodesic q 1 = z := (exp_eq_geodesic y v).symm.trans hv
   change dist (c y) (c z) ≤ C*dist y z
   simpa only [Function.comp_apply,geodesic_zero,hq1,sub_zero,norm_one,mul_one,hn,
     dist_eq_norm,q,norm_sub_rev] using hd
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
