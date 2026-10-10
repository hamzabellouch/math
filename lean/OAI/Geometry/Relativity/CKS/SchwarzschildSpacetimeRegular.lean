import OAI.Geometry.Relativity.CKS.SchwarzschildSpacetimeAlgebra

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
local instance : IsBoundedSMul ℝ SpacetimeBilinear :=
  @NormedSpace.toIsBoundedSMul ℝ SpacetimeBilinear _ _ _

lemma advancedMetric_smoothAt (m : ℝ) {z : Spacetime} (hx : z.2 ≠ 0) :
    ContDiffAt ℝ ∞ (advancedMetric m) z := by
  have hsp : ContDiffAt ℝ ∞ (fun y : Spacetime => y.2) z := contDiffAt_snd
  have hn := (contDiffAt_norm ℝ hx).comp z hsp (n := ∞)
  have hH : ContDiffAt ℝ ∞ (fun y : Spacetime => schwarzschildH m ‖y.2‖) z :=
    contDiffAt_const.sub (contDiffAt_const.div hn (norm_ne_zero_iff.mpr hx))
  have hR : ContDiffAt ℝ ∞ (fun y : Spacetime => radiusForm y.2) z := by
    exact (((innerSL ℝ).contDiff.contDiffAt.comp z ((radialUnit_smoothAt hx).comp z hsp)).clm_comp contDiffAt_const)
  exact ((((hH.neg.smul contDiffAt_const).add (contDiffAt_const.smulRight hR)).add
    (hR.smulRight contDiffAt_const)).add contDiffAt_const).sub (hR.smulRight hR)

lemma advancedMetric_symm (m : ℝ) (z a b : Spacetime) :
    advancedMetric m z a b = advancedMetric m z b a := by
  rw [advancedMetric_apply,advancedMetric_apply,real_inner_comm a.2 b.2]
  ring

lemma advancedMetric_nondegenerate (m : ℝ) {z : Spacetime} (hx : z.2 ≠ 0)
    (a : Spacetime) (ha : ∀ b : Spacetime, advancedMetric m z a b = 0) : a = 0 := by
  have hr := ha (0,radialUnit z.2)
  rw [advancedMetric_apply] at hr
  simp only [mul_zero,zero_mul,zero_add,add_zero,radialUnit_inner_self hx,mul_one,
    real_inner_comm a.2 (radialUnit z.2)] at hr
  have ht : a.1 = 0 := by linarith
  have ht' := ha (1,0)
  rw [advancedMetric_apply] at ht'
  simp only [ht,zero_mul,inner_zero_right,mul_zero,zero_add,add_zero,one_mul,sub_zero] at ht'
  have hb := ha (0,a.2)
  rw [advancedMetric_apply] at hb
  simp only [ht,ht',zero_add,mul_zero,sub_zero] at hb
  have ha2 : a.2 = 0 := (inner_self_eq_zero).mp hb
  exact Prod.ext ht ha2

lemma advancedGraph_smoothAt {m : ℝ} (hm : 0 < m) {x : E3} (hr : m < ‖x‖) :
    ContDiffAt ℝ ∞ (advancedGraph m) x := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_trans hm hr)
  have h := (advancedTime_smooth hm).contDiffAt (isOpen_Ioi.mem_nhds hr)
  exact (h.comp x (contDiffAt_norm ℝ hx)).prodMk contDiffAt_id

lemma advancedGraph_injective (m : ℝ) : Function.Injective (advancedGraph m) := by
  intro x y h
  exact congrArg Prod.snd h

lemma advancedTime_horizon (m : ℝ) : advancedTime m (2*m) = 0 := by
  simp [advancedTime]
lemma advancedSlope_horizon {m : ℝ} (hm : 0 < m) : advancedSlope m (2*m) = 1/2 := by
  rw [advancedSlope,lapse_horizon hm,velocity_near m (2*m) (by linarith)]
  norm_num
end CKSSchwarzschild

end

end OAI
