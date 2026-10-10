import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselSlopeNumerics

namespace OAI

/-! A certified lower bound at the first theta frequency. -/
noncomputable section
open MeasureTheory Set Filter
namespace CubicFirstMoment

lemma cubicWhittakerFirstSlope_lower {v : ℝ} (hv : 0<v)
    (hx : 2≤4*Real.pi*v) (hx' : 4*Real.pi*v≤5/2) :
    (81/1000:ℝ)≤ -(cubicThetaWhittakerDerivative v).re := by
  let F := cubicWhittakerNegativeSlope v
  have hi := cubicWhittakerNegativeSlope_integral hv
  have hc : Continuous F := by unfold F cubicWhittakerNegativeSlope; fun_prop
  have hnon : ∀ u,0≤F u := cubicWhittakerNegativeSlope_nonneg (by linarith)
  have habs : (fun u => F |u|)=F := by
    funext u
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_nonpos hu]
      exact cubicWhittakerNegativeSlope_even v u
  have heven : (∫ u : ℝ,F u)=2*(∫ u in Ioi 0,F u) := by
    simpa only [habs] using (integral_comp_abs (f:=F))
  have he : -(cubicThetaWhittakerDerivative v).re=∫ u in Ioi 0,F u := by
    rw [hi.2,heven]
    ring
  have hbound (a b q : ℝ) (ha : 0≤a) (hab : a≤b)
      (hq : (4*Real.pi*v)*Real.cosh b≤q) :
      (b-a)*((q-1)*Real.exp (-q))≤∫ u in Ioc a b,F u := by
    apply cubicWhittakerNegativeSlope_interval_lower hv hx hab
    intro u hu
    have hu0 : 0≤u := ha.trans hu.1.le
    have hb0 : 0≤b := ha.trans hab
    have hcosh : Real.cosh u≤Real.cosh b := Real.cosh_le_cosh.mpr (by
      rw [abs_of_nonneg hu0,abs_of_nonneg hb0]; exact hu.2)
    exact (mul_le_mul_of_nonneg_left hcosh (by linarith)).trans hq
  have h01 := hbound 0 (1/2) 3 (by norm_num) (by norm_num) (by
    nlinarith [cubic_cosh_half_le,Real.cosh_pos (1/2:ℝ)])
  have h12 := hbound (1/2) 1 4 (by norm_num) (by norm_num) (by
    nlinarith [cubic_cosh_one_le,Real.cosh_pos (1:ℝ)])
  have h23 := hbound 1 (3/2) 6 (by norm_num) (by norm_num) (by
    nlinarith [cubic_cosh_three_halves_le,Real.cosh_pos (3/2:ℝ)])
  have hs1 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hc.intervalIntegrable 0 (1/2)) (hc.intervalIntegrable (1/2) 1)
  have hs2 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 (3/2))
  rw [intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_of_le (by norm_num)] at hs1 hs2
  have hm : (∫ u in Ioc (0:ℝ) (3/2),F u)≤∫ u in Ioi 0,F u := by
    apply setIntegral_mono_set (hi.1.integrableOn (s:=Ioi 0))
      (Eventually.of_forall hnon)
    exact Eventually.of_forall (fun _ hu => hu.1)
  have h3 : (1/21:ℝ)≤Real.exp (-3) := by
    rw [Real.exp_neg]
    simpa using (inv_le_inv₀ (by norm_num : (0:ℝ)<21) (Real.exp_pos 3)).mpr cubic_exp_three_le
  have h4 : (1/55:ℝ)≤Real.exp (-4) := by
    rw [Real.exp_neg]
    simpa using (inv_le_inv₀ (by norm_num : (0:ℝ)<55) (Real.exp_pos 4)).mpr cubic_exp_four_le
  have h6 : (1/405:ℝ)≤Real.exp (-6) := by
    rw [Real.exp_neg]
    simpa using (inv_le_inv₀ (by norm_num : (0:ℝ)<405) (Real.exp_pos 6)).mpr cubic_exp_six_le
  rw [he]
  norm_num at h01 h12 h23
  linarith

end CubicFirstMoment

end

end OAI
