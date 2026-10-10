import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.CostGeodesicTaylor

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

 theorem cost_normal_smooth (x : M) {v : TangentSpace (model n) x} (hv : v ∈ injectivityDomain x) :
     ContDiffAt ℝ ∞ (fun h : TangentSpace (model n) x => cost (exp x h) (exp x v)) 0 := by
   have hc := cost_smooth_at_injectivity x hv
   have he : ContMDiffAt 𝓘(ℝ,TangentSpace (model n) x) ((model n).prod (model n)) ∞
       (fun h => (exp x h,exp x v)) 0 := (exp_fibre_smooth x).contMDiffAt.prodMk contMDiffAt_const
   have hc' : ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ,ℝ) ∞
       (fun q : M×M => cost q.1 q.2) (exp x (0 : TangentSpace (model n) x),exp x v) := by
     simpa only [exp_zero] using hc
   exact contMDiffAt_iff_contDiffAt.mp (hc'.comp 0 he)

 theorem cost_normal_gradient (x : M) {v : TangentSpace (model n) x} (hv : v ∈ injectivityDomain x) :
     HasFDerivAt (fun h : TangentSpace (model n) x => cost (exp x h) (exp x v)) (-(innerSL ℝ v)) 0 := by
   let f : TangentSpace (model n) x → ℝ := fun h => cost (exp x h) (exp x v)
   have hf : HasFDerivAt f (fderiv ℝ f 0) 0 :=
     ((cost_normal_smooth x hv).differentiableAt (by simp)).hasFDerivAt
   have hgrad (ξ : TangentSpace (model n) x) : fderiv ℝ f 0 ξ = -inner ℝ v ξ := by
     have hline : HasDerivAt (fun t : ℝ => f (t•ξ)) (fderiv ℝ f 0 ξ) 0 := by
       have hh := hf.comp_hasDerivAt_of_eq 0 ((hasDerivAt_id (0:ℝ)).smul_const ξ) (by simp)
       simpa only [one_smul,Function.comp_def,id_eq,f] using hh
     let l : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
     have hl : Tendsto l atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
     have hpos (j : ℕ) : 0 < l j := one_div_pos.mpr (by positivity)
     have hl' : Tendsto l atTop (𝓝[≠] (0:ℝ)) :=
       tendsto_nhdsWithin_iff.mpr ⟨hl,Eventually.of_forall (fun j => (hpos j).ne')⟩
     have hd := hline.tendsto_slope_zero.comp hl'
     have hd' : Tendsto (fun j => (cost (exp x (l j•ξ)) (exp x v)-cost x (exp x v))/l j)
         atTop (𝓝 (fderiv ℝ f 0 ξ)) := by
       simpa only [f,zero_add,zero_smul,exp_zero,smul_eq_mul,Function.comp_def,div_eq_mul_inv,mul_comm] using hd
     have ht := cost_geodesic_first_limit x hv ξ (tendsto_const_nhds (x := exp x v)) hl
       (Eventually.of_forall (fun j => (hpos j).ne'))
     exact tendsto_nhds_unique hd' ht
   have heq : fderiv ℝ f 0 = -(innerSL ℝ v) := by
     ext ξ
     exact hgrad ξ
   rw [← heq]
   exact hf
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
