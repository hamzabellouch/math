import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.OuterVelocityFactorNonneg

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval ContDiff

namespace WeakMTWTransport

lemma outerTemplate_eq_primitive {M0 K eta s:ℝ} (heta : 0 < eta) (hs : s ≤ 1-eta) :
    outerTemplate M0 K eta s=outerPrimitive M0 K eta s := by
  have H : (s-(1-eta))/eta ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) heta.le
  simp only [outerTemplate,Real.smoothTransition.zero_of_nonpos H,sub_zero,mul_one]

lemma outerTemplate_zero {M0 K eta s:ℝ} (heta : 0 < eta) (hs : 1 ≤ s) :
    outerTemplate M0 K eta s=0 := by
  have H : 1 ≤ (s-(1-eta))/eta := (le_div_iff₀ heta).mpr (by linarith only [hs])
  simp only [outerTemplate,Real.smoothTransition.one_of_one_le H,sub_self,mul_zero]

lemma outerTemplate_nonneg {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta)
    (heta1 : eta ≤ 1/128) (hetasmall : eta ≤ templateEps/(24*(128*(M0+3)*(K+1)))) :
    0 ≤ outerTemplate M0 K eta s := by
  have H := (outerPrimitive_bounds (s := s) hM hK heta heta1 hetasmall).1
  have hJ : 0 ≤ outerPrimitive M0 K eta s := by rw [templateEps_eq] at H; linarith only [H]
  exact mul_nonneg hJ (sub_nonneg.mpr (Real.smoothTransition.le_one _))

lemma outerTemplate_lower {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta)
    (heta1 : eta ≤ 1/128) (hetasmall : eta ≤ templateEps/(24*(128*(M0+3)*(K+1))))
    (hs : s ≤ 1-eta) : 1 ≤ outerTemplate M0 K eta s := by
  rw [outerTemplate_eq_primitive heta hs]
  have H := (outerPrimitive_bounds (s := s) hM hK heta heta1 hetasmall).1
  rw [templateEps_eq] at H
  linarith only [H]

lemma outerTemplate_upper {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta)
    (heta1 : eta ≤ 1/128) (hetasmall : eta ≤ templateEps/(24*(128*(M0+3)*(K+1)))) :
    outerTemplate M0 K eta s ≤ 2*M0+8 := by
  obtain ⟨H1,H2⟩ := outerPrimitive_bounds (s := s) hM hK heta heta1 hetasmall
  rw [templateEps_eq] at H1 H2
  have hJ : 0 ≤ outerPrimitive M0 K eta s := by linarith only [H1]
  have H := mul_le_mul_of_nonneg_left
    (show 1-Real.smoothTransition ((s-(1-eta))/eta) ≤ 1 by
      linarith only [Real.smoothTransition.nonneg ((s-(1-eta))/eta)]) hJ
  change outerTemplate M0 K eta s ≤ outerPrimitive M0 K eta s*1 at H
  linarith only [H,H2]

lemma outerTemplate_zero_level {M0 K eta:ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1/128) :
    outerTemplate M0 K eta 0=1+templateEps/2 := by
  rw [outerTemplate_eq_primitive heta (by linarith only [heta1])]
  simp [outerPrimitive]

lemma centerTemplate_le_outer {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta)
    (heta1 : eta ≤ 1/128) (hetasmall : eta ≤ templateEps/(24*(128*(M0+3)*(K+1)))) :
    centerTemplate s ≤ outerTemplate M0 K eta s := by
  by_cases hs : s ≤ 1-eta
  · exact (centerTemplate_bounds s).2.le.trans (outerTemplate_lower hM hK heta heta1 hetasmall hs)
  · exact (centerTemplate_right (by linarith only [hs,heta1])).le.trans
      (outerTemplate_nonneg hM hK heta heta1 hetasmall)

lemma outerPrimitive_core_gain {M0 K eta:ℝ} (hK : 1 ≤ K) (heta : 0 < eta) :
    outerPrimitive M0 K eta (1/(128*(K+1)))-outerPrimitive M0 K eta 0 =
      M0+3-1/(32768*(K+1)) := by
  let h : ℝ := 1/(128*(K+1))
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have H : (∫ q in (0:ℝ)..h,outerVelocity M0 K eta q)=
      ∫ q in (0:ℝ)..h,(128*(M0+3)*(K+1)-(K+1)*q) := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le hh] at hq
    exact outerVelocity_core heta (by linarith only [hq.1,heta]) hq.2 hK
  rw [outerPrimitive_sub,H]
  rw [intervalIntegral.integral_sub intervalIntegrable_const (show IntervalIntegrable (fun q : ℝ => (K+1)*q) volume 0 h from
      (show Continuous (fun q : ℝ => (K+1)*q) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
  simp only [sub_zero,zero_pow (by norm_num : 2≠0),smul_eq_mul]
  dsimp [h]
  have hk : K+1≠0 := by linarith only [hK]
  field_simp
  ring

lemma outerTemplate_barrier {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta)
    (heta1 : eta ≤ 1/128) (hs : 1/16 ≤ s) (hs' : s ≤ 1-eta) :
    outerTemplate M0 K eta 0+1 ≤ outerTemplate M0 K eta s := by
  have hk : 0 < K+1 := by linarith only [hK]
  have hh : 1/(128*(K+1)) ≤ s := by
    have H : 1/(128*(K+1)) ≤ 1/16 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hK])
    exact H.trans hs
  have hcorr : 1/(32768*(K+1)) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hK])
  have H := outerPrimitive_core_gain (M0 := M0) hK heta
  have Hm := outerPrimitive_monotone (eta := eta) hM hK hh
  rw [outerTemplate_eq_primitive heta hs',outerTemplate_eq_primitive heta (by linarith only [heta1])]
  linarith only [H,Hm,hcorr,hM]

end WeakMTWTransport

end

end OAI
