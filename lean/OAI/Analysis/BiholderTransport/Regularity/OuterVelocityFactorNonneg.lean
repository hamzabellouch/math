import Mathlib
import OAI.Analysis.BiholderTransport.Contact.MiddleExclusion

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval ContDiff

namespace WeakMTWTransport

lemma outerVelocity_factor_nonneg {M0 K s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K)
    (hs : s ≤ 2*(1/(128*(K+1)))) :
    0 ≤ 128*(M0+3)*(K+1)-(K+1)*s := by
  have hk : 0 < K+1 := by linarith
  have hu : 2*(1/(128*(K+1))) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hv : s ≤ 128*(M0+3) := le_trans (hs.trans hu) (by linarith)
  have H := mul_nonneg hk.le (sub_nonneg.mpr hv)
  nlinarith only [H]

lemma outerVelocity_nonneg {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) :
    0 ≤ outerVelocity M0 K eta s := by
  by_cases hs : 2*(1/(128*(K+1))) ≤ s
  · rw [outerVelocity_zero_right hK hs]
  · exact mul_nonneg (mul_nonneg (outerVelocity_factor_nonneg hM hK (le_of_not_ge hs))
      (Real.smoothTransition.nonneg _)) (sub_nonneg.mpr (Real.smoothTransition.le_one _))

lemma outerVelocity_le_factor {M0 K eta s:ℝ}
    (hf : 0 ≤ 128*(M0+3)*(K+1)-(K+1)*s) :
    outerVelocity M0 K eta s ≤ 128*(M0+3)*(K+1)-(K+1)*s := by
  have h1 := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one ((s+3*eta)/eta)) hf
  have h2 := mul_le_mul_of_nonneg_left
    (show 1-Real.smoothTransition ((s-1/(128*(K+1)))/(1/(128*(K+1)))) ≤ 1 from by
      linarith only [Real.smoothTransition.nonneg ((s-1/(128*(K+1)))/(1/(128*(K+1))))])
    (mul_nonneg hf (Real.smoothTransition.nonneg ((s+3*eta)/eta)))
  simpa only [mul_one,outerVelocity] using h2.trans (by simpa only [mul_one] using h1)

lemma outerVelocity_le {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta) :
    outerVelocity M0 K eta s ≤ 128*(M0+3)*(K+1)+3*(K+1)*eta := by
  have hk : 0 < K+1 := by linarith
  by_cases hl : s ≤ -3*eta
  · rw [outerVelocity_zero_left heta hl]
    positivity
  by_cases hr : 2*(1/(128*(K+1))) ≤ s
  · rw [outerVelocity_zero_right hK hr]
    positivity
  have H := outerVelocity_le_factor (eta := eta)
    (outerVelocity_factor_nonneg hM hK (le_of_not_ge hr))
  have HH := mul_nonneg hk.le (show 0 ≤ s+3*eta by linarith only [hl])
  nlinarith only [H,HH]

lemma outerVelocity_le_L {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (hs : 0 ≤ s) :
    outerVelocity M0 K eta s ≤ 128*(M0+3)*(K+1) := by
  by_cases hr : 2*(1/(128*(K+1))) ≤ s
  · rw [outerVelocity_zero_right hK hr]
    positivity
  have H := outerVelocity_le_factor (eta := eta)
    (outerVelocity_factor_nonneg hM hK (le_of_not_ge hr))
  have HH := mul_nonneg (show 0 ≤ K+1 by linarith) hs
  linarith only [H,HH]

lemma hasDerivAt_outerPrimitive (M0 K eta s:ℝ) :
    HasDerivAt (outerPrimitive M0 K eta) (outerVelocity M0 K eta s) s := by
  have hc := (outerVelocity_smooth M0 K eta).continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

lemma outerPrimitive_smooth (M0 K eta:ℝ) : ContDiff ℝ ∞ (outerPrimitive M0 K eta) := by
  have hd : deriv (outerPrimitive M0 K eta)=outerVelocity M0 K eta :=
    funext (fun s => (hasDerivAt_outerPrimitive M0 K eta s).deriv)
  have HH : ContDiff ℝ ((∞:ℕ∞ω)+1) (outerPrimitive M0 K eta) := by
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨fun s => (hasDerivAt_outerPrimitive M0 K eta s).differentiableAt,?_,?_⟩
    · simp
    · rw [hd]
      exact outerVelocity_smooth M0 K eta
  simpa using HH

lemma outerTemplate_smooth (M0 K eta:ℝ) : ContDiff ℝ ∞ (outerTemplate M0 K eta) := by
  unfold outerTemplate
  exact (outerPrimitive_smooth M0 K eta).mul (contDiff_const.sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const eta)))

lemma outerPrimitive_monotone {M0 K eta:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) :
    Monotone (outerPrimitive M0 K eta) := by
  apply monotone_of_deriv_nonneg (fun s => (hasDerivAt_outerPrimitive M0 K eta s).differentiableAt)
  intro s
  rw [(hasDerivAt_outerPrimitive M0 K eta s).deriv]
  exact outerVelocity_nonneg hM hK

lemma outerPrimitive_sub (M0 K eta a b:ℝ) :
    outerPrimitive M0 K eta b-outerPrimitive M0 K eta a=
      ∫ q in a..b,outerVelocity M0 K eta q := by
  have hc := (outerVelocity_smooth M0 K eta).continuous
  have H := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 a)
    (hc.intervalIntegrable a b)
  unfold outerPrimitive
  linarith only [H]

lemma outerPrimitive_flat_left {M0 K eta s:ℝ} (heta : 0 < eta) (hs : s ≤ -3*eta) :
    outerPrimitive M0 K eta s=outerPrimitive M0 K eta (-3*eta) := by
  have H := outerPrimitive_sub M0 K eta s (-3*eta)
  have Hz : (∫ q in s..(-3*eta),outerVelocity M0 K eta q)=0 := by
    calc
      _=∫ _q in s..(-3*eta),(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro q hq
        rw [uIcc_of_le hs] at hq
        exact outerVelocity_zero_left heta hq.2
      _=0 := by simp
  linarith only [H,Hz]

lemma outerPrimitive_flat_right {M0 K eta s:ℝ} (hK : 1 ≤ K)
    (hs : 2*(1/(128*(K+1))) ≤ s) :
    outerPrimitive M0 K eta s=outerPrimitive M0 K eta (2*(1/(128*(K+1)))) := by
  have H := outerPrimitive_sub M0 K eta (2*(1/(128*(K+1)))) s
  have Hz : (∫ q in (2*(1/(128*(K+1))))..s,outerVelocity M0 K eta q)=0 := by
    calc
      _=∫ _q in (2*(1/(128*(K+1))))..s,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro q hq
        rw [uIcc_of_le hs] at hq
        exact outerVelocity_zero_right hK hq.1
      _=0 := by simp
  linarith only [H,Hz]

lemma outerPrimitive_bounds {M0 K eta s:ℝ} (hM : 2 ≤ M0) (hK : 1 ≤ K) (heta : 0 < eta)
    (heta1 : eta ≤ 1/128) (hetasmall : eta ≤ templateEps/(24*(128*(M0+3)*(K+1)))) :
    1+templateEps/4 ≤ outerPrimitive M0 K eta s ∧
      outerPrimitive M0 K eta s ≤ 1+templateEps/2+2*(M0+3) := by
  have hk : 0 < K+1 := by linarith
  have hL : 0 < 128*(M0+3)*(K+1) := by positivity
  have hLbig : 3*(K+1)*eta ≤ 128*(M0+3)*(K+1) := by
    have HH := mul_nonneg hk.le (show 0 ≤ 128*(M0+3)-3*eta by linarith only [hM,heta1])
    nlinarith only [HH]
  have he : 6*eta*(128*(M0+3)*(K+1)) ≤ templateEps/4 := by
    have HH := (le_div_iff₀ (show 0 < 24*(128*(M0+3)*(K+1)) by positivity)).mp hetasmall
    nlinarith only [HH]
  have hc := (outerVelocity_smooth M0 K eta).continuous
  have Hleft := intervalIntegral.integral_mono_on (show -3*eta ≤ 0 by linarith)
    (hc.intervalIntegrable (μ := volume) (-3*eta) 0) (continuous_const.intervalIntegrable (-3*eta) 0)
    (fun q _ => outerVelocity_le (s := q) hM hK heta)
  rw [intervalIntegral.integral_const] at Hleft
  simp only [smul_eq_mul] at Hleft
  have Hjleft : 1+templateEps/4 ≤ outerPrimitive M0 K eta (-3*eta) := by
    rw [outerPrimitive,intervalIntegral.integral_symm]
    nlinarith only [Hleft,hLbig,he,heta.le]
  have hh : 0 ≤ 2*(1/(128*(K+1))) := by positivity
  have Hright := intervalIntegral.integral_mono_on hh
    (hc.intervalIntegrable (μ := volume) 0 (2*(1/(128*(K+1)))))
    (continuous_const.intervalIntegrable 0 (2*(1/(128*(K+1)))))
    (fun q hq => outerVelocity_le_L (eta := eta) hM hK hq.1)
  rw [intervalIntegral.integral_const] at Hright
  simp only [sub_zero,smul_eq_mul] at Hright
  have heq : 2*(1/(128*(K+1)))*(128*(M0+3)*(K+1))=2*(M0+3) := by
    field_simp
  rw [heq] at Hright
  have Hjright : outerPrimitive M0 K eta (2*(1/(128*(K+1)))) ≤ 1+templateEps/2+2*(M0+3) := by
    unfold outerPrimitive
    linarith only [Hright]
  constructor
  · by_cases hs : s ≤ -3*eta
    · rwa [outerPrimitive_flat_left heta hs]
    · exact Hjleft.trans (outerPrimitive_monotone (eta := eta) hM hK (le_of_not_ge hs))
  · by_cases hs : 2*(1/(128*(K+1))) ≤ s
    · rwa [outerPrimitive_flat_right hK hs]
    · exact (outerPrimitive_monotone (eta := eta) hM hK (le_of_not_ge hs)).trans Hjright

end WeakMTWTransport

end

end OAI
