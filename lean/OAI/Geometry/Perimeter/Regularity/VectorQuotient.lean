import OAI.Geometry.Perimeter.Regularity.EllipticDifference

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

 def vectorQuotient (G : Euc n → V) (e : Euc n) (s : ℝ) (x : Euc n) : V :=
  s⁻¹•(G (x+s•e)-G x)

omit [CompleteSpace V] in
 theorem vectorQuotient_continuous [CompleteSpace V] {G : Euc n → V} (hG : Continuous G) (e : Euc n) (s : ℝ) :
    Continuous (vectorQuotient G e s) :=
  continuous_const.smul ((hG.comp (continuous_id.add continuous_const)).sub hG)

 theorem vectorQuotient_integral {G : Euc n → V} (hG : ContDiff ℝ 1 G)
    (e : Euc n) {s : ℝ} (hs : s≠0) (x : Euc n) :
    vectorQuotient G e s x = ∫ t in (0:ℝ)..1, fderiv ℝ G (x+t•(s•e)) e := by
  have hc : Continuous (fun t : ℝ ↦ fderiv ℝ G (x+t•(s•e)) e) :=
    ((hG.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ ↦ G (x+u•(s•e)))
      (s•fderiv ℝ G (x+t•(s•e)) e) t := by
    have hh := (hG.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const (s•e) |>.const_add x)
    simpa only [map_smul,one_smul,id_eq,Function.comp_def] using hh
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    ((continuous_const.smul hc).intervalIntegrable 0 1)
  simp only [intervalIntegral.integral_smul,zero_smul,add_zero,one_smul] at hh
  rw [vectorQuotient,←hh,smul_smul,inv_mul_cancel₀ hs,one_smul]

 theorem vectorQuotient_bound {G : Euc n → V} (hG : ContDiff ℝ 1 G)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ x, ‖fderiv ℝ G x‖ ≤ L)
    (e : Euc n) (s : ℝ) (x : Euc n) : ‖vectorQuotient G e s x‖ ≤ L*‖e‖ := by
  by_cases hs : s=0
  · simp only [vectorQuotient,hs,inv_zero,zero_smul,norm_zero]
    positivity
  rw [vectorQuotient_integral hG e hs]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (fun t _ ↦
    ((fderiv ℝ G (x+t•(s•e))).le_opNorm e).trans
      (mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)))
  simpa using hh

 theorem vectorQuotient_difference {G : Euc n → V} (hG : ContDiff ℝ 1 G)
    (e : Euc n) {s : ℝ} (hs : s≠0) (x y : Euc n) {C : ℝ}
    (h : ∀ t∈Icc (0:ℝ) 1,
      ‖fderiv ℝ G (x+t•(s•e))-fderiv ℝ G (y+t•(s•e))‖ ≤ C) :
    ‖vectorQuotient G e s x-vectorQuotient G e s y‖ ≤ C*‖e‖ := by
  have hc (x : Euc n) : Continuous (fun t : ℝ ↦ fderiv ℝ G (x+t•(s•e)) e) :=
    ((hG.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  rw [vectorQuotient_integral hG e hs,vectorQuotient_integral hG e hs,
    ←intervalIntegral.integral_sub ((hc x).intervalIntegrable 0 1) ((hc y).intervalIntegrable 0 1)]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht ↦ by
    have ht' : t∈Icc (0:ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      exact Ioc_subset_Icc_self ht
    change ‖(fderiv ℝ G (x+t•(s•e))-fderiv ℝ G (y+t•(s•e))) e‖ ≤ C*‖e‖
    exact (ContinuousLinearMap.le_opNorm _ e).trans
      (mul_le_mul_of_nonneg_right (h t ht') (norm_nonneg _)))
  simpa using hh

omit [CompleteSpace V] in
 theorem compact_C1_fderiv_bound [CompleteSpace V] {G : Euc n → V} (hG : ContDiff ℝ 1 G)
    (hgc : HasCompactSupport G) : ∃ L : ℝ, 0 ≤ L ∧ ∀ x, ‖fderiv ℝ G x‖ ≤ L := by
  have hc := hG.continuous_fderiv (by simp)
  have hcc := hgc.fderiv ℝ
  obtain ⟨L,hL⟩ := hcc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max 0 L,le_max_left _ _,fun x ↦ ?_⟩
  by_cases hx : x∈tsupport (fderiv ℝ G)
  · exact (hL x hx).trans (le_max_right _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    exact le_max_left _ _

end RPISingularHarnack

end

end OAI
