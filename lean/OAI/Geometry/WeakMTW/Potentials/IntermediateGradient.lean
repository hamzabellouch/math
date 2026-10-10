import Mathlib
import OAI.Geometry.WeakMTW.Potentials.IntermediateRegularity

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

 local instance tangentFinite (x : M) : FiniteDimensional ℝ (TangentSpace (model n) x) :=
   VectorBundle.finiteDimensional ℝ (Model n) _ x
 local instance tangentComplete (x : M) : CompleteSpace (TangentSpace (model n) x) :=
   FiniteDimensional.complete ℝ _

 def normalGradient (f : M → ℝ) (x : M) : TangentSpace (model n) x :=
   (InnerProductSpace.toDual ℝ (TangentSpace (model n) x)).symm
     (fderiv ℝ (fun h : TangentSpace (model n) x => f (exp x h)) 0)

 theorem normalGradient_of_upper_support {f : M → ℝ} {x : M} {v : TangentSpace (model n) x}
     (hv : v ∈ minimizingDomain x) {t : ℝ} (ht : 0 < t)
     (hf : DifferentiableAt ℝ (fun h : TangentSpace (model n) x => f (exp x h)) 0)
     (hs : ∀ z, f z ≤ f x+(cost z (exp x v)-cost x (exp x v))/t) :
     normalGradient f x = (-t⁻¹)•v := by
   have hi := strict_radial_mem_injectivity hv (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
   let F (h : TangentSpace (model n) x) := f x+(2/t)*(cost (exp x h) (exp x ((1/2:ℝ)•v))-cost x (exp x ((1/2:ℝ)•v)))
   have hD : HasFDerivAt F (innerSL ℝ ((-t⁻¹)•v)) 0 := by
     have hh := (((cost_normal_gradient x hi).sub_const
       (cost x (exp x ((1/2:ℝ)•v)))).const_mul (2/t)).const_add (f x)
     have he : (2/t)•(-(innerSL ℝ ((1/2:ℝ)•v))) = innerSL ℝ ((-t⁻¹)•v) := by
       ext w
       simp only [smul_apply,neg_apply,
         innerSL_apply_apply,inner_smul_left,conj_trivial,smul_eq_mul]
       ring
     rw [he] at hh
     exact hh
   have hmin : IsLocalMin (fun h => F h-f (exp x h)) 0 := by
     apply Eventually.of_forall
     intro h
     have hc := div_le_div_of_nonneg_right (shortened_upper_difference hv
       (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1) (exp x h)) ht.le
     change F 0-f (exp x (0 : TangentSpace (model n) x)) ≤ _
     simp only [F,exp_zero,sub_self,mul_zero,add_zero]
     have hconv : (cost (exp x h) (exp x ((1/2:ℝ)•v))-cost x (exp x ((1/2:ℝ)•v)))/(1/2)/t =
         (2/t)*(cost (exp x h) (exp x ((1/2:ℝ)•v))-cost x (exp x ((1/2:ℝ)•v))) := by ring
     rw [hconv] at hc
     linarith [hs (exp x h)]
   have heq := sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero (hD.sub hf.hasFDerivAt))
   apply (InnerProductSpace.toDual ℝ (TangentSpace (model n) x)).injective
   simp only [normalGradient,LinearIsometryEquiv.apply_symm_apply]
   exact heq.symm

 theorem backward_vector_minimizing {q : TangentBundle (model n) M} (hq : q ∈ totalMinimizingSet)
     {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
     (-t)•(geodesicFlow t q).2 ∈ minimizingDomain (geodesicFlow t q).1 ∧
       exp (geodesicFlow t q).1 ((-t)•(geodesicFlow t q).2) = q.1 := by
   have he : exp (geodesicFlow t q).1 ((-t)•(geodesicFlow t q).2) = q.1 := by
     rw [exp_flow,neg_add_cancel,geodesic_zero]
   refine ⟨?_,he⟩
   change dist (geodesicFlow t q).1 (exp (geodesicFlow t q).1 ((-t)•(geodesicFlow t q).2)) = _
   rw [he,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg ht,geodesicFlow_norm,dist_comm]
   have hd := minimizing_shortened_dist hq (s := 0) (t := t) (le_refl 0) ht ht1
   change dist q.1 (geodesic q t) = _
   simpa only [zero_smul,exp_zero,sub_zero,exp_mul_eq_geodesic] using hd

 theorem intermediate_gradient_state (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (huv : IsDualPair u v) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
     (q : potentialGraph (n := n) u) :
     (⟨potentialProjection u t q,normalGradient (hopfLax t u) (potentialProjection u t q)⟩ : TangentBundle (model n) M) =
       geodesicFlow t q.val := by
   have hq : q.val ∈ totalMinimizingSet := ((globalSupportingProperty hMTW ⟨v,huv.2.1,huv.2.2.1⟩).1
     q.val.1 q.val.2 q.property).1
   have he : potentialProjection u t q = (geodesicFlow t q.val).1 := exp_mul_eq_geodesic q.val t
   rw [he]
   have hb := backward_vector_minimizing hq ht.le ht1.le
   have hc := intermediate_c11 hMTW huv ht ht1
   have hn : DifferentiableAt ℝ (fun h : TangentSpace (model n) (geodesicFlow t q.val).1 =>
       hopfLax t u (exp (geodesicFlow t q.val).1 h)) 0 := by
     have h := hc.1.comp ((exp_fibre_smooth (geodesicFlow t q.val).1).of_le (by simp : (1:ℕ∞ω) ≤ ∞))
     exact (contMDiffAt_iff_contDiffAt.mp (h 0)).differentiableAt (by norm_num)
   have hgrad := normalGradient_of_upper_support hb.1 ht hn (fun z => by
     rw [hb.2]
     have hs := intermediate_two_sided_supports hMTW huv ht ht1 q
     rw [he] at hs
     rw [cost_comm z q.val.1,cost_comm (geodesicFlow t q.val).1 q.val.1,sub_div]
     linarith [(hs.1 z).2,hs.2.1])
   have hg : normalGradient (hopfLax t u) (geodesicFlow t q.val).1 = (geodesicFlow t q.val).2 := by
     rw [hgrad,smul_smul,neg_mul_neg,inv_mul_cancel₀ ht.ne',one_smul]
   exact TotalSpace.ext rfl (heq_of_eq hg)

 theorem intermediate_pole_flow (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (huv : IsDualPair u v) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (z : M) :
     ((potentialHomeomorph hMTW ⟨v,huv.2.1,huv.2.2.1⟩ ht ht1).symm z).val =
       geodesicFlow (-t) (⟨z,normalGradient (hopfLax t u) z⟩ : TangentBundle (model n) M) := by
   let e := potentialHomeomorph hMTW ⟨v,huv.2.1,huv.2.2.1⟩ ht ht1
   have h := intermediate_gradient_state hMTW huv ht ht1 (e.symm z)
   have he : potentialProjection u t (e.symm z) = z := e.apply_symm_apply z
   rw [he] at h
   rw [h,←geodesicFlow_add,neg_add_cancel,geodesicFlow_zero]
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
