import Mathlib
import OAI.Geometry.WeakMTW.Potentials.OrdinarySubgradientCapture
import OAI.Geometry.WeakMTW.Coordinates.CostNormalGradient

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 omit [IsManifold (model n) ∞ M]
   [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
   [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem ordinarySubdiff_of_smooth_support {u : M → ℝ} {x : M} {p : TangentSpace (model n) x}
     {f : TangentSpace (model n) x → ℝ} (hf : HasFDerivAt f (innerSL ℝ p) 0)
     (hc : f 0 = u x) (hle : ∀ h, f h ≤ u (exp x h)) : p ∈ ordinarySubdiff u x := by
   intro ε hε
   have he := hf.isLittleO.bound hε
   obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp he
   refine ⟨δ,hδ,fun h hh => ?_⟩
   have hrem := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hh)
   simp only [Set.mem_ofPred_eq,sub_zero,hc,innerSL_apply_apply,Real.norm_eq_abs] at hrem
   have hlo := (abs_le.mp hrem).1
   linarith [hle h]

 omit [IsManifold (model n) ∞ M]
   [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
   [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem ordinarySubdiff_convex (u : M → ℝ) (x : M) : Convex ℝ (ordinarySubdiff (n := n) u x) := by
   intro p hp q hq a b ha hb hab ε hε
   obtain ⟨δ₀,hδ₀,h₀⟩ := hp ε hε
   obtain ⟨δ₁,hδ₁,h₁⟩ := hq ε hε
   refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,fun h hh => ?_⟩
   have hp' := mul_le_mul_of_nonneg_left (h₀ h (hh.trans_le (min_le_left _ _))) ha
   have hq' := mul_le_mul_of_nonneg_left (h₁ h (hh.trans_le (min_le_right _ _))) hb
   simp only [inner_add_left,inner_smul_left,conj_trivial]
   have hsum := add_le_add hp' hq'
   have hleft : a * (u x + inner ℝ p h - ε * ‖h‖) + b * (u x + inner ℝ q h - ε * ‖h‖) =
       u x + (a * inner ℝ p h + b * inner ℝ q h) - ε * ‖h‖ := by
     calc _ = (a+b)*u x+(a*inner ℝ p h+b*inner ℝ q h)-(a+b)*(ε*‖h‖) := by ring
          _ = _ := by rw [hab]; ring
   have hright : a * u (exp x h)+b * u (exp x h) = u (exp x h) := by
     rw [← add_mul,hab,one_mul]
   rwa [hleft,hright] at hsum

 theorem interior_cost_support_subgradient {u : M → ℝ} {x : M}
     {a : TangentSpace (model n) x} (ha : a ∈ injectivityDomain x) (k : ℝ)
     (hs : ∀ z, u x+k*(cost x (exp x a)-cost z (exp x a)) ≤ u z) :
     k•a ∈ ordinarySubdiff u x := by
   let F : TangentSpace (model n) x → ℝ := fun w =>
     u x+k*(cost x (exp x a)-cost (exp x w) (exp x a))
   have hd := cost_normal_gradient x ha
   have hF : HasFDerivAt F (innerSL ℝ (k•a)) 0 := by
     have hh := ((hd.neg.const_add (cost x (exp x a))).const_mul k).const_add (u x)
     have hh' := hh.congr_of_eventuallyEq (f₁ := F) (Eventually.of_forall (fun w => by
       simp only [F,sub_eq_add_neg,Pi.neg_apply]))
     have heq : k • - -(innerSL ℝ) a = (innerSL ℝ) (k•a) := by
       ext ξ
       simp only [smul_apply,
         innerSL_apply_apply,inner_smul_left,conj_trivial,smul_eq_mul,neg_neg]
     rw [heq] at hh'
     exact hh'

   apply ordinarySubdiff_of_smooth_support hF
   · simp [F,exp_zero]
   · exact fun w => hs (exp x w)

 theorem potentialActive_mem_ordinarySubdiff {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v)
     {x : M} {a : TangentSpace (model n) x} (ha : a ∈ potentialActive u v x) :
     a ∈ ordinarySubdiff u x := by
   have hi := strict_radial_mem_injectivity ha.1 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
   have hs := interior_cost_support_subgradient hi (2:ℝ) (fun z => by
     have h := potentialActive_shortened_support hv hu ha (by norm_num : (0:ℝ) < 1/2)
       (by norm_num : (1/2:ℝ) < 1) z
     convert h using 1
     ring)
   simpa only [smul_smul,show (2:ℝ)*(1/2) = 1 by norm_num,one_smul] using hs

 theorem ordinarySubdiff_eq_activeHull {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v) (x : M) :
     ordinarySubdiff (n := n) u x = convexHull ℝ (potentialActive u v x) := by
   apply Subset.antisymm (ordinarySubdiff_subset_activeHull hv hu x)
   exact convexHull_min (fun _ ha => potentialActive_mem_ordinarySubdiff hv hu ha) (ordinarySubdiff_convex u x)
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
