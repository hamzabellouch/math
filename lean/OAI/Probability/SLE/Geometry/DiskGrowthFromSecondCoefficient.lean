import OAI.Probability.SLE.Loewner.UnivalentRadialDerivative
import OAI.Probability.SLE.Multipoint.MultipointGeometry

namespace OAI

/-! Integrating the sharp second-coefficient estimate gives the growth
bounds for normalized univalent disk maps. -/
noncomputable section
open Set Filter Metric Function MeasureTheory
open scoped Topology

namespace SLEExactGauge

theorem diskGrowth_of_secondDerivative
    (hsecond : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) →
      InjOn f (ball 0 1) → ‖deriv (deriv f) 0‖≤4*‖deriv f 0‖) :
    PublishedDiskUnivalentGrowth := by
  intro f hf hi z hz
  by_cases hz0 : z=0
  · simp [hz0]
  let r := ‖z‖
  have hrp : 0<r := norm_pos_iff.mpr hz0
  have hr1 : r<1 := mem_ball_zero_iff.mp hz
  let u := z/(r:ℂ)
  have hu : ‖u‖=1 := by
    dsimp [u,r]
    simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm]
    exact div_self (norm_ne_zero_iff.mpr hz0)
  have hru : (r:ℂ)*u=z := by
    dsimp [u]
    field_simp [Complex.ofReal_ne_zero.mpr hrp.ne']
  have hpre := fun (a : ℂ) (ha : ‖a‖<1) =>
    univalent_preSchwarzian_of_second_derivative hsecond hf hi (a := a) ha
  let v (t : ℝ) := f ((t:ℂ)*u)
  let v' (t : ℝ) := u*deriv f ((t:ℂ)*u)
  let g (t : ℝ) := ‖deriv f 0‖*(1+t)/(1-t)^3
  let G (t : ℝ) := ‖deriv f 0‖*t/(1-t)^2
  have hat (t : ℝ) (ht : t∈Icc 0 r) : (t:ℂ)*u∈ball 0 1 := by
    rw [mem_ball_zero_iff,norm_mul,hu,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact ht.2.trans_lt hr1
  have hv' (t : ℝ) (ht : t∈Icc 0 r) : HasDerivAt v (v' t) t := by
    have hd := ((hf.differentiableAt (isOpen_ball.mem_nhds (hat t ht))).hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const u)
    simpa only [ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul,Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul,Function.comp_def,v,v'] using hd
  have hv'c : ContinuousOn v' (Icc 0 r) := by
    apply continuousOn_const.mul
    intro t ht
    have houter : ContinuousAt (deriv f) ((t:ℂ)*u) :=
      (hf.analyticAt (isOpen_ball.mem_nhds (hat t ht))).deriv.continuousAt
    exact (ContinuousAt.comp (g := deriv f) (f := fun s : ℝ => (s:ℂ)*u)
      houter (by fun_prop)).continuousWithinAt
  have hgc : ContinuousOn g (Icc 0 r) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact pow_ne_zero _ (by linarith [ht.2,hr1])
  have hG (t : ℝ) (ht : t∈Icc 0 r) : HasDerivAt G (g t) t := by
    have hm : 1-t≠0 := by linarith [ht.2,hr1]
    have h := ((hasDerivAt_id t).const_mul ‖deriv f 0‖).div
      (((hasDerivAt_id t).const_sub 1).pow 2) (pow_ne_zero _ hm)
    change HasDerivAt G _ t at h
    convert h using 1
    dsimp [g]
    field_simp
    ring
  have hvint : ∫ t in (0:ℝ)..r, v' t=f z-f 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := r)
      (fun t ht => hv' t (by simpa only [uIcc_of_le hrp.le] using ht))
      (hv'c.intervalIntegrable_of_Icc hrp.le)
    simpa only [v,hru,Complex.ofReal_zero,zero_mul] using h
  have hgint : ∫ t in (0:ℝ)..r, g t=G r := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := r)
      (fun t ht => hG t (by simpa only [uIcc_of_le hrp.le] using ht))
      (hgc.intervalIntegrable_of_Icc hrp.le)
    simpa [G] using h
  calc
    ‖f z-f 0‖ = ‖∫ t in (0:ℝ)..r, v' t‖ := congrArg norm hvint.symm
    _ ≤ ∫ t in (0:ℝ)..r, ‖v' t‖ := intervalIntegral.norm_integral_le_integral_norm hrp.le
    _ ≤ ∫ t in (0:ℝ)..r, g t := by
      apply intervalIntegral.integral_mono_on hrp.le
        (hv'c.norm.intervalIntegrable_of_Icc hrp.le) (hgc.intervalIntegrable_of_Icc hrp.le)
      intro t ht
      dsimp only [v']
      rw [norm_mul,hu,one_mul]
      exact univalent_radial_derivative_bound hf hi hpre u hu t ⟨ht.1,ht.2.trans_lt hr1⟩
    _ = ‖deriv f 0‖*‖z‖/(1-‖z‖)^2 := hgint

end SLEExactGauge

end

end OAI
