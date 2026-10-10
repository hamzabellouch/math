import Mathlib

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma exists_tame_volterra_majorant {D C F : ℝ} (hD : 0≤D) (hC : 0≤C) (hF : 0≤F) :
    ∃ H : ℝ → ℝ, Continuous H ∧ Monotone H ∧ (∀ t, 0≤t → 1≤H t) ∧
      ∀ t, 0≤t → D+C*(∫ u in Icc (0:ℝ) t, 1+(F+1)*(1+H u))≤H t := by
  let ell := 2*C*(F+2)+1
  let H : ℝ → ℝ := fun t => (D+1)*Real.exp (ell*t)
  have hell : 0≤ell := by dsimp [ell]; positivity
  have hH : Continuous H := continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hmon : Monotone H := fun a b hab => mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hell)) (by positivity)
  have hH1 (t : ℝ) (ht : 0≤t) : 1≤H t := by
    have h0 : H 0=D+1 := by simp [H]
    have hh := hmon ht
    rw [h0] at hh
    linarith
  have hd (t : ℝ) : HasDerivAt H (ell*H t) t := by
    convert (((Real.hasDerivAt_exp (ell*t)).comp t ((hasDerivAt_id t).const_mul ell)).const_mul (D+1)) using 1
    · rfl
    · dsimp [H]
      ring
  refine ⟨H,hH,hmon,hH1,?_⟩
  intro t ht
  have hb (u : ℝ) (hu : 0≤u) : C*(1+(F+1)*(1+H u))≤ell*H u := by
    have h1 := hH1 u hu
    have hfirst : 1+(F+1)*(1+H u)≤(F+2)*(1+H u) := by linarith
    have hsecond : (F+2)*(1+H u)≤2*(F+2)*H u := by nlinarith [mul_nonneg (by linarith : 0≤F+2) (by linarith : 0≤H u-1)]
    calc
      C*(1+(F+1)*(1+H u))≤C*(2*(F+2)*H u) := mul_le_mul_of_nonneg_left (hfirst.trans hsecond) hC
      _ ≤ ell*H u := by dsimp [ell]; nlinarith
  have hleft : Continuous (fun u => C*(1+(F+1)*(1+H u))) := by fun_prop
  have hright : Continuous (fun u => ell*H u) := continuous_const.mul hH
  have hi := setIntegral_mono_on (μ:=volume) (hleft.continuousOn.integrableOn_compact isCompact_Icc)
    (hright.continuousOn.integrableOn_compact isCompact_Icc) measurableSet_Icc
    (fun u (hu : u∈Icc (0:ℝ) t) => hb u hu.1)
  have he : (∫ u in Icc (0:ℝ) t, ell*H u)=H t-(D+1) := by
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hright.intervalIntegrable 0 t)]
    simp [H]
  rw [integral_const_mul,he] at hi
  linarith

end RVM
end

end OAI
