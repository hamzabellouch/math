import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma contDiff_primitive {f:ℝ → ℝ} (hf:ContDiff ℝ ∞ f) (a:ℝ) :
    ContDiff ℝ ∞ (fun s=>∫ q in a..s,f q) := by
  apply contDiff_infty_iff_deriv.mpr
  have hd:∀s,HasDerivAt (fun t=>∫ q in a..t,f q) (f s) s:=fun s=>
    intervalIntegral.integral_hasDerivAt_right (hf.continuous.intervalIntegrable _ _)
      hf.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuous.continuousAt
  exact ⟨fun s=>(hd s).differentiableAt,by simpa only [funext (fun s=>(hd s).deriv)] using hf⟩

def outerW (K M η s:ℝ):ℝ :=
  (128*(M+3)*(K+1)-(K+1)*s)*Real.smoothTransition ((s+3*η)/η)*
    (1-Real.smoothTransition ((s-1/(128*(K+1)))/(1/(128*(K+1)))))

def outerJ (K M η s:ℝ):ℝ := 1+(1/2048:ℝ)+∫ q in (0:ℝ)..s,outerW K M η q

def outerProfile (K M η s:ℝ):ℝ :=
  outerJ K M η s*(1-Real.smoothTransition ((s-(1-η))/η))

lemma outerW_contDiff (K M η:ℝ) : ContDiff ℝ ∞ (outerW K M η) := by
  unfold outerW
  exact ((contDiff_const.sub (contDiff_const.mul contDiff_id)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _))).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)))

lemma outerJ_contDiff (K M η:ℝ) : ContDiff ℝ ∞ (outerJ K M η) :=
  contDiff_const.add (contDiff_primitive (outerW_contDiff K M η) 0)

lemma outerProfile_contDiff (K M η:ℝ) : ContDiff ℝ ∞ (outerProfile K M η) := by
  unfold outerProfile
  exact (outerJ_contDiff K M η).mul (contDiff_const.sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)))

lemma outerJ_hasDerivAt (K M η s:ℝ) : HasDerivAt (outerJ K M η) (outerW K M η s) s := by
  have hc:Continuous (outerW K M η):=(outerW_contDiff K M η).continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

lemma outerW_zero_right {K M η s:ℝ} (hK:1≤K) (hs:2/(128*(K+1))≤ s) : outerW K M η s=0 := by
  have hh:0<1/(128*(K+1)):=by positivity
  have hs' : 2*(1/(128*(K+1))) ≤ s := by convert hs using 1; ring
  unfold outerW
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hh).mpr (by linarith only [hs']))]
  ring

lemma outerW_nonneg {K M η:ℝ} (hK:1≤K) (hM:2≤M) (_:0<η) (s:ℝ) :
    0≤outerW K M η s := by
  by_cases hs:2/(128*(K+1))≤ s
  · rw [outerW_zero_right hK hs]
  · have hs':s<2/(128*(K+1)):=lt_of_not_ge hs
    have hb:2/(128*(K+1))<128*(M+3):=by
      apply (div_lt_iff₀ (by positivity : 0<128*(K+1))).mpr
      nlinarith
    dsimp only [outerW]
    exact mul_nonneg (mul_nonneg (by nlinarith) (Real.smoothTransition.nonneg _))
      (sub_nonneg.mpr (Real.smoothTransition.le_one _))

lemma outerJ_monotone {K M η:ℝ} (hK:1≤K) (hM:2≤M) (hη:0<η) :
    Monotone (outerJ K M η) := by
  apply monotone_of_deriv_nonneg ((outerJ_contDiff K M η).differentiable (by simp))
  intro s
  rw [(outerJ_hasDerivAt K M η s).deriv]
  exact outerW_nonneg hK hM hη s

lemma outerW_affine {K M η s:ℝ} (hK:1≤K) (hη:0<η)
    (hs₁:-2*η≤ s) (hs₂:s≤1/(128*(K+1))) :
    outerW K M η s=128*(M+3)*(K+1)-(K+1)*s := by
  have hh:0<1/(128*(K+1)):=by positivity
  unfold outerW
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hη).mpr (by linarith)),
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le)]
  ring

lemma outerProfile_left {K M η s:ℝ} (hη:0<η) (hs:s≤1-η) :
    outerProfile K M η s=outerJ K M η s := by
  unfold outerProfile
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le)]
  ring

lemma outerJ_zero (K M η:ℝ) : outerJ K M η 0=1+(1/2048:ℝ) := by
  simp only [outerJ,intervalIntegral.integral_same,add_zero]

end WeakMTWTransport

end

end OAI
