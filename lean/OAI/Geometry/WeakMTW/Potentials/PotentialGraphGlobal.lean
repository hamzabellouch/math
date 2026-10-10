import Mathlib
import OAI.Geometry.WeakMTW.Potentials.OrdinarySubgradientIdentity
import OAI.Geometry.WeakMTW.Potentials.PotentialFiniteReduction

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

 theorem potentialGraph_compact {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v) :
     IsCompact (potentialGraph (n := n) u) := by
   have huc : Continuous u := hu ▸ cTransform_continuous hv
   have heq : potentialGraph (n := n) u = tangentHull (potentialActiveGraph u v) := by
     ext q
     change q.2 ∈ ordinarySubdiff u q.1 ↔ q.2 ∈ convexHull ℝ (potentialActive u v q.1)
     rw [ordinarySubdiff_eq_activeHull hv hu]
   have hclosed : IsClosed (potentialGraph (n := n) u) := by
     rw [heq]
     exact tangentHull_closed (potentialActiveGraph_compact huc hv)
   apply (tangent_disk_compact (n := n) (M := M) (Metric.diam (univ : Set M))).of_isClosed_subset hclosed
   intro q hq
   have hsub : potentialActive (n := n) u v q.1 ⊆ Metric.closedBall 0 (Metric.diam (univ : Set M)) := by
     intro a ha
     rw [Metric.mem_closedBall,dist_zero_right,← show dist q.1 (exp q.1 a) = ‖a‖ from ha.1]
     exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
   have hh : q.2 ∈ convexHull ℝ (potentialActive u v q.1) := ordinarySubdiff_subset_activeHull (n := n) hv hu q.1 hq
   have hm := convexHull_min hsub (convex_closedBall (0 : TangentSpace (model n) q.1) _) hh
   simpa only [Set.mem_ofPred_eq,Metric.mem_closedBall,dist_zero_right] using hm

 theorem minimizing_pole_ordinary {u : M → ℝ} {x : M} {w : TangentSpace (model n) x}
     (hw : w ∈ minimizingDomain x) {s : ℝ} (hs : 0 < s)
     (hmin : ∀ z, cost x (exp x w)+s*u x ≤ cost z (exp x w)+s*u z) :
     s⁻¹•w ∈ ordinarySubdiff u x := by
   have hi := strict_radial_mem_injectivity hw (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
   have hsupport (z : M) : u x+(2/s)*(cost x (exp x ((1/2:ℝ)•w))-cost z (exp x ((1/2:ℝ)•w))) ≤ u z := by
     have hsplit := shortened_upper_difference hw (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1) z
     have hh := hmin z
     apply (mul_le_mul_iff_right₀ hs).mp
     have hcancel : s*(2/s) = 2 := by field_simp
     rw [mul_add,← mul_assoc,hcancel]
     linarith
   have h := interior_cost_support_subgradient hi (2/s) hsupport
   have heq : (2/s)*(1/2:ℝ) = s⁻¹ := by field_simp
   simpa only [smul_smul,heq] using h

 theorem potentialProjection_surjective {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v)
     {s : ℝ} (hs : 0 < s) : Function.Surjective (potentialProjection (n := n) u s) := by
   intro z
   let : Nonempty M := ⟨z⟩
   have hc : Continuous (fun x : M => cost x z+s*u x) :=
     (cost_continuous.comp (continuous_id.prodMk continuous_const)).add
       (continuous_const.mul (hu ▸ cTransform_continuous hv))
   obtain ⟨x,_hx,hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
   obtain ⟨w,hw,hn⟩ := exists_minimizing_vector (n := n) x z
   have hwm : w ∈ minimizingDomain x := by
     change dist x (exp x w) = ‖w‖
     rw [hw,hn]
   have hp : s⁻¹•w ∈ ordinarySubdiff u x := minimizing_pole_ordinary hwm hs (by
     intro z'; rw [hw]; exact hmin (mem_univ z'))
   refine ⟨⟨⟨x,s⁻¹•w⟩,hp⟩,?_⟩
   change exp x (s•(s⁻¹•w)) = z
   simpa only [smul_smul,mul_inv_cancel₀ hs.ne',one_smul] using hw

 theorem potentialProjection_injective (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v)
     {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
     Function.Injective (potentialProjection (n := n) u s) := by
   rintro ⟨⟨x,a⟩,ha⟩ ⟨⟨z,b⟩,hb⟩ he
   change exp x (s•a) = exp z (s•b) at he
   have ha' : a ∈ convexHull ℝ (potentialActive u v x) :=
     ordinarySubdiff_subset_activeHull hv hu x ha
   have hb' : b ∈ convexHull ℝ (potentialActive u v z) :=
     ordinarySubdiff_subset_activeHull hv hu z hb
   have hpa := potential_activeHull_intermediate hMTW hv hu ha' hs hs1
   have hqb := potential_activeHull_intermediate hMTW hv hu hb' hs hs1
   have hzx : z = x := by
     apply (hpa.2 z).2
     have h₁ := (hpa.2 z).1
     have h₂ := (hqb.2 x).1
     rw [← he] at h₂
     exact le_antisymm h₂ h₁
   subst z
   have hab : s•a = s•b := exp_injOn_injectivity x hpa.1 hqb.1 he
   have hab' : a = b := by
     simpa only [smul_smul,inv_mul_cancel₀ hs.ne',one_smul] using congrArg (fun v => s⁻¹•v) hab
   subst b
   rfl

 theorem potentialProjection_homeomorph (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (hv : Continuous v) (hu : u = cTransform v)
     {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
     IsHomeomorph (potentialProjection (n := n) u s) := by
   let : CompactSpace (potentialGraph (n := n) u) := isCompact_iff_compactSpace.mp (potentialGraph_compact (n := n) hv hu)
   have hc : Continuous (potentialProjection (n := n) u s) :=
     scaledExp_continuous.comp (continuous_const.prodMk continuous_subtype_val)
   exact isHomeomorph_iff_continuous_bijective.mpr
     ⟨hc,potentialProjection_injective hMTW hv hu hs hs1,potentialProjection_surjective hv hu hs⟩

 theorem globalSupportingProperty (hMTW : HasWeakMTW (n := n) (M := M))
     {u : M → ℝ} (hu : IsPotential u) : GlobalSupportingProperty (n := n) u := by
   obtain ⟨v,hv,hu⟩ := hu
   constructor
   · intro x p hp
     exact potential_activeHull_support hMTW hv hu (ordinarySubdiff_subset_activeHull hv hu x hp)
   · intro t ht ht1
     refine ⟨potentialProjection_homeomorph hMTW hv hu ht ht1,fun q => ?_⟩
     have hq := potential_activeHull_intermediate hMTW hv hu
       (ordinarySubdiff_subset_activeHull hv hu q.val.1 q.property) ht ht1
     refine ⟨hq.1,fun x' => ⟨?_,?_⟩⟩
     · apply (mul_le_mul_iff_left₀ ht).mp
       change (u q.val.1+cost q.val.1 (exp q.val.1 (t•q.val.2))/t)*t ≤
         (u x'+cost x' (exp q.val.1 (t•q.val.2))/t)*t
       simp only [add_mul,div_mul_cancel₀ _ ht.ne']
       nlinarith [(hq.2 x').1]
     · intro heq
       apply (hq.2 x').2
       have heq' := congrArg (fun a : ℝ => a*t) heq
       change (u x'+cost x' (exp q.val.1 (t•q.val.2))/t)*t =
         (u q.val.1+cost q.val.1 (exp q.val.1 (t•q.val.2))/t)*t at heq'
       simp only [add_mul,div_mul_cancel₀ _ ht.ne'] at heq'
       nlinarith
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
