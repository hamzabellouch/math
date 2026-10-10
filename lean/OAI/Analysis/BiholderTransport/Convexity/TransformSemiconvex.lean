import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ActiveHull
import OAI.Analysis.BiholderTransport.Contact.Inner
import OAI.Analysis.BiholderTransport.LinearAlgebra.HalfCostUniform

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
section TransformSemiconvex
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma uniform_cTransform_semiconvex (a : M) :
    ∃ K>0, ∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ v : M → ℝ, Continuous v →
        ConvexOn ℝ (ball (extChartAt 𝓘(ℝ,Model n) a a) r)
          (fun z => cTransform v ((extChartAt 𝓘(ℝ,Model n) a).symm z)+K/2*‖z‖^2) := by
  obtain ⟨B,hB,r,hr,hrT,hjet⟩ := uniform_half_cost_hessian (n := n) a
  refine ⟨4*B,by positivity,r,hr,hrT,?_⟩
  intro v hv
  have he : 4*B/2=2*B := by ring
  rw [he]
  apply convexOn_of_quadratic_lower_supports (convex_ball _ _)
  intro x hx
  let χ := extChartAt 𝓘(ℝ,Model n) a
  obtain ⟨p,hp⟩ := nonempty_activeLogs (n := n) hv (χ.symm x)
  let f := chartCost (n := n) a (riemannianExp (χ.symm x) ((1/2:ℝ) • p))
  refine ⟨(-2:ℝ) • fderiv ℝ f x,?_⟩
  intro z hz
  have hrem := first_order_remainder_le_of_hessian_bound (convex_ball _ _) hB.le
    (fun w hw => (hjet x hx p hp.1 w hw).1)
    (fun w hw => (hjet x hx p hp.1 w hw).2) hx hz
  have hlow := active_split_lower_support hv hp.1 hp.2
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) (χ.symm z)
  change |f z-f x-fderiv ℝ f x (z-x)|≤B*‖z-x‖^2 at hrem
  change -(f z-f x)/(1/2:ℝ)≤cTransform v (χ.symm z)-cTransform v (χ.symm x) at hlow
  have hU := (abs_le.mp hrem).2
  simp only [_root_.smul_apply,smul_eq_mul]
  norm_num at hlow
  nlinarith

end TransformSemiconvex
end WeakMTWTransport

end

end

end

end OAI
