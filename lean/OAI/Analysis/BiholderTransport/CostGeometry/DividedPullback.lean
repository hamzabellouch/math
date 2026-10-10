import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.StationaryPullback

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma divided_cost_difference_pullback {z : M} {p : TangentSpace 𝓘(ℝ,Model n) z}
    {t : ℝ} {g : E → TangentSpace 𝓘(ℝ,Model n) z} {a : E}
    (hp : p∈injectivityDomain z) (htp : t • p∈injectivityDomain z) (ht : t≠0)
    (hg : ContDiffAt ℝ 2 g a) (hg0 : g a=0) (k : E) :
    fderiv ℝ (fderiv ℝ (fun b =>
      normalCost z (t • p) (g b)/t-normalCost z p (g b))) a k k =
    hessianValue z (t • p) (fderiv ℝ g a k)/t-
      hessianValue z p (fderiv ℝ g a k) := by
  let F := fun v => t⁻¹*normalCost z (t • p) v-normalCost z p v
  have hA := (normalCost_contDiffAt htp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hB := (normalCost_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hF : ContDiffAt ℝ 2 F 0 := (contDiffAt_const.mul hA).sub hB
  have hzero : fderiv ℝ F 0=0 := by
    ext v
    rw [fderiv_fun_sub ((hA.differentiableAt (by norm_num)).const_mul _)
      (hB.differentiableAt (by norm_num))]
    change (fderiv ℝ (t⁻¹ • normalCost z (t • p)) 0) v-
      fderiv ℝ (normalCost z p) 0 v=0
    rw [fderiv_const_smul_field]
    simp only [Pi.smul_apply,smul_apply,smul_eq_mul,
      normalCost_fderiv_zero htp,normalCost_fderiv_zero hp,real_inner_smul_left]
    field_simp [ht]
    ring
  have HH := second_fderiv_comp_stationary (g := g)
    (by simpa only [hg0] using hF) hg (by simpa only [hg0] using hzero) k k
  rw [hg0,second_fderiv_sub (contDiffAt_const.mul hA) hB,
    second_fderiv_const_mul] at HH
  rw [hessianValue_eq_normalHessian htp,hessianValue_eq_normalHessian hp]
  simpa only [F,normalHessian,div_eq_mul_inv,mul_comm] using HH
end WeakMTWTransport

end

end OAI
