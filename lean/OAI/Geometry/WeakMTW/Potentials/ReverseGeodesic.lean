import Mathlib
import OAI.Geometry.WeakMTW.Potentials.LiftedSections

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem exp_flow (q : TangentBundle (model n) M) (s t : ℝ) :
     exp (geodesicFlow t q).1 (s•(geodesicFlow t q).2) = geodesic q (s+t) := by
   rw [exp_mul_eq_geodesic,geodesic_shift]

 def reverseState (q : TangentBundle (model n) M) : TangentBundle (model n) M :=
   mulState (-1) (geodesicFlow 1 q)

 theorem reverseState_base (q : TangentBundle (model n) M) :
     (reverseState q).1 = exp q.1 q.2 := (exp_eq_geodesic _ _).symm

 theorem reverseState_exp (q : TangentBundle (model n) M) (s : ℝ) :
     exp (reverseState q).1 (s•(reverseState q).2) = geodesic q (1-s) := by
   change exp (geodesicFlow 1 q).1 (s•((-1 : ℝ)•(geodesicFlow 1 q).2)) = _
   rw [smul_smul,exp_flow]
   congr 1
   ring

 theorem reverseState_norm (q : TangentBundle (model n) M) : ‖(reverseState q).2‖ = ‖q.2‖ := by
   change ‖(-1 : ℝ)•(geodesicFlow 1 q).2‖ = _
   rw [neg_one_smul, norm_neg, geodesicFlow_norm]

 theorem reverseState_minimizing {q : TangentBundle (model n) M} (hq : q ∈ totalMinimizingSet) :
     reverseState q ∈ totalMinimizingSet := by
   change dist (reverseState q).1 (exp (reverseState q).1 (reverseState q).2) = _
   have he := reverseState_exp q 1
   simp only [one_smul,sub_self,geodesic_zero] at he
   rw [reverseState_norm,he,reverseState_base,dist_comm]
   exact hq

 omit [IsManifold (model n) ∞ M]
   [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
   [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
   [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem cost_smooth_swap {x y : M}
     (h : ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ,ℝ) ∞
       (fun q : M×M => cost q.1 q.2) (x,y)) :
     ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ,ℝ) ∞
       (fun q : M×M => cost q.1 q.2) (y,x) := by
    simpa only [Function.comp_def, cost_comm] using
      h.comp (y,x) (contMDiffAt_snd.prodMk contMDiffAt_fst)

 theorem cost_smooth_shortened {q : TangentBundle (model n) M} (hq : q ∈ totalMinimizingSet)
     {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
     ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ,ℝ) ∞
       (fun r : M×M => cost r.1 r.2) (q.1,exp q.1 (t•q.2)) ∧
     ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ,ℝ) ∞
       (fun r : M×M => cost r.1 r.2) (exp q.1 (t•q.2),exp q.1 q.2) := by
   refine ⟨cost_smooth_at_injectivity q.1 (strict_radial_mem_injectivity hq ht.le ht1),?_⟩
   have hr := reverseState_minimizing hq
   have hi := strict_radial_mem_injectivity hr (sub_pos.mpr ht1).le (by linarith : 1-t < 1)
   have hc := cost_smooth_swap (cost_smooth_at_injectivity (reverseState q).1 hi)
   have he : exp (reverseState q).1 ((1-t)•(reverseState q).2) = exp q.1 (t•q.2) := by
     rw [reverseState_exp,sub_sub_cancel,exp_mul_eq_geodesic]
   simpa only [he,reverseState_base] using hc
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
