import Mathlib
import OAI.Geometry.WeakMTW.Potentials.GradientCoordinates
import OAI.Geometry.WeakMTW.Potentials.IntermediateUniformRegularity

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 local instance realNormedCovectors : NormedSpace ℝ (Model n) := inferInstance

 theorem intermediate_gradient_norm_le (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (huv : IsDualPair u v) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (z : M) :
     ‖normalGradient (n := n) (hopfLax t u) z‖ ≤ Metric.diam (univ : Set M) := by
   let e := potentialHomeomorph hMTW ⟨v,huv.2.1,huv.2.2.1⟩ ht ht1
   let q := e.symm z
   have h := intermediate_gradient_state hMTW huv ht ht1 q
   have he : potentialProjection u t q = z := e.apply_symm_apply z
   rw [he] at h
   have hn := congrArg (fun p : TangentBundle (model n) M => ‖p.2‖) h
   change ‖normalGradient (n := n) (hopfLax t u) z‖ = ‖(geodesicFlow t q.val).2‖ at hn
   rw [geodesicFlow_norm] at hn
   have hq := ((globalSupportingProperty hMTW ⟨v,huv.2.1,huv.2.2.1⟩).1 q.val.1 q.val.2 q.property).1
   change dist q.val.1 (exp q.val.1 q.val.2) = ‖q.val.2‖ at hq
   rw [hn,←hq]
   exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)

 theorem coordinate_differential_eq {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ,ℝ) 1 f)
     (x y : M) (hy : y ∈ (chartAt (Model n) x).source) :
     fderiv ℝ (fun X => f ((chartAt (Model n) x).symm X)) (chartAt (Model n) x y) =
       metric x (chartAt (Model n) x y)
         (stateChart x (⟨y,normalGradient f y⟩ : TangentBundle (model n) M)).2 := by
   rw [normalGradient_coordinates hf x y hy]
   exact ((metric_invertible (fun _ hv => metric_positive x ((chartAt (Model n) x).map_source hy) hv)).self_apply_inverse _).symm

 theorem intermediate_covector_center_bound (hMTW : HasWeakMTW (n := n) (M := M)) (z : M) :
     ∃ D : ℝ, 0 ≤ D ∧ ∀ u v : M → ℝ, IsDualPair u v → ∀ t : ℝ, 0 < t → t < 1 →
       ‖fderiv ℝ (fun X => hopfLax t u ((chartAt (Model n) z).symm X)) (chartAt (Model n) z z)‖ ≤ D := by
   let c := chartAt (Model n) z
   let B := ContinuousLinearMap.opNorm (mfderiv (model n) (model n) c z)
   have hB : 0 ≤ B := (mfderiv (model n) (model n) c z).opNorm_nonneg
   let D := ‖metric z (c z)‖*B*Metric.diam (univ : Set M)
   refine ⟨D,mul_nonneg (mul_nonneg (metric z (c z)).opNorm_nonneg hB)
     Metric.diam_nonneg,?_⟩
   intro u v huv t ht ht1
   let w := normalGradient (n := n) (hopfLax t u) z
   have hw := intermediate_gradient_norm_le hMTW huv ht ht1 z
   have hch := congrArg (fun p : TangentBundle (model n) (Model n) => p.2)
     (tangentMap_chart (p := (⟨z,0⟩ : TangentBundle (model n) M))
       (q := (⟨z,w⟩ : TangentBundle (model n) M)) (mem_chart_source (Model n) z))
   change mfderiv (model n) (model n) c z w = (stateChart z ⟨z,w⟩).2 at hch
   rw [coordinate_differential_eq (intermediate_c11 hMTW huv ht ht1).1 z z (mem_chart_source (Model n) z)]
   change ‖metric z (c z) (stateChart z ⟨z,w⟩).2‖ ≤ D
   rw [←hch]
   calc
     _ ≤ ‖metric z (c z)‖*‖mfderiv (model n) (model n) c z w‖ := (metric z (c z)).le_opNorm _
     _ ≤ ‖metric z (c z)‖*(B*‖w‖) := mul_le_mul_of_nonneg_left
       ((mfderiv (model n) (model n) c z).le_opNorm w) (norm_nonneg (metric z (c z)))
     _ ≤ D := by
       dsimp only [D]
       rw [mul_assoc]
       exact mul_le_mul_of_nonneg_left
         (mul_le_mul_of_nonneg_left hw hB) (norm_nonneg (metric z (c z)))

 theorem intermediate_covector_bounds (hMTW : HasWeakMTW (n := n) (M := M))
     {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (z : M) :
     ∃ r : ℝ, ∃ C : ℝ≥0, ∃ K : ℝ, 0 < r ∧ 0 < K ∧
       Metric.ball (chartAt (Model n) z z) r ⊆ (chartAt (Model n) z).target ∧
       ∀ u v : M → ℝ, IsDualPair u v → ∀ t ∈ Icc a b,
       LipschitzOnWith C (fderiv ℝ (fun X => hopfLax t u ((chartAt (Model n) z).symm X)))
         (Metric.ball (chartAt (Model n) z z) r) ∧
       ∀ X ∈ Metric.ball (chartAt (Model n) z z) r,
         ‖fderiv ℝ (fun Y => hopfLax t u ((chartAt (Model n) z).symm Y)) X‖ ≤ K := by
   obtain ⟨r,C,hr,hT,hL⟩ := intermediate_uniform_coordinate_c11 hMTW ha hab hb z
   obtain ⟨D,hD,hDb⟩ := intermediate_covector_center_bound hMTW z
   refine ⟨r,C,C*r+D+1,hr,by positivity,hT,?_⟩
   intro u v huv t ht
   refine ⟨hL u v huv t ht,?_⟩
   intro X hX
   have hh := (hL u v huv t ht).dist_le_mul (x := X) hX (y := chartAt (Model n) z z) (Metric.mem_ball_self hr)
   have hc := hDb u v huv t (ha.trans_le ht.1) (ht.2.trans_lt hb)
   have hb' := dist_triangle (fderiv ℝ (fun Y => hopfLax t u ((chartAt (Model n) z).symm Y)) X)
     (fderiv ℝ (fun Y => hopfLax t u ((chartAt (Model n) z).symm Y)) (chartAt (Model n) z z)) 0
   simp only [dist_zero_right] at hb'
   have hm := mul_le_mul_of_nonneg_left hX.le C.coe_nonneg
   linarith
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
