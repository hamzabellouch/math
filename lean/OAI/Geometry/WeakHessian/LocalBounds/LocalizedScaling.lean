import Mathlib
import OAI.Geometry.WeakHessian.Measure.CurvatureTail
import OAI.Geometry.WeakHessian.Transport.LocalizedActionBound

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter
open scoped Topology

def localActionLimit (c CG s : ℝ) : ℝ :=
  1+c*s+2*|c| *s*(Real.exp (2*CG*s)-1)+4*c^2*s^2

lemma localizedActionBound_nonneg {K a c CG T : ℝ} (ha : 0 ≤ a) (hCG : 0 ≤ CG) (hT : 0 ≤ T) :
    0 ≤ localizedActionBound K a c CG T := by
  have hM := localizedHeatM_one_le (K := K) ha hCG hT
  have HR : 0 ≤ 2*|K-a*c| *T*(localizedHeatM K a CG T-1) := by positivity
  unfold localizedActionBound
  nlinarith [sq_nonneg ((K-a*c)*T-1/8)]

lemma localizedActionBound_scaled {K c CG s T : ℝ} (hT : 0 < T) :
    localizedActionBound K (s/T) c CG T =
      1-(K*T-s*c)+2*|K*T-s*c| *(Real.exp (2*(|K| *T+s*CG))-1)+4*(K*T-s*c)^2 := by
  have he : (K-s/T*c)*T = K*T-s*c := by field_simp
  have heM : (|K|+s/T*CG)*T = |K| *T+s*CG := by field_simp
  have ha : |K-s/T*c| *T = |K*T-s*c| := by rw [← he,abs_mul,abs_of_pos hT]
  unfold localizedActionBound localizedHeatM
  rw [show 2*(|K|+s/T*CG)*T = 2*(|K| *T+s*CG) by linarith only [heM]]
  calc
    _ = 1-(K-s/T*c)*T+2*(|K-s/T*c| *T)*(Real.exp (2*(|K| *T+s*CG))-1)+4*((K-s/T*c)*T)^2 := by ring
    _ = _ := by rw [he,ha]

lemma localizedActionBound_scaling_limit (K c CG : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun T : ℝ => localizedActionBound K (s/T) c CG T) (𝓝[>] 0) (𝓝 (localActionLimit c CG s)) := by
  have H := (show ContinuousAt (fun T : ℝ =>
      1-(K*T-s*c)+2*|K*T-s*c| *(Real.exp (2*(|K| *T+s*CG))-1)+4*(K*T-s*c)^2) 0 from by fun_prop).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have He : 1-(K*0-s*c)+2*|K*0-s*c| *(Real.exp (2*(|K| *0+s*CG))-1)+4*(K*0-s*c)^2 = localActionLimit c CG s := by
    simp only [localActionLimit,mul_zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg hs,zero_add,neg_sq]
    ring_nf
  rw [He] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with T hT
  exact (localizedActionBound_scaled hT).symm

lemma localized_small_scaled_eventually {K c CG s : ℝ}
    (hs : 8*s*(CG+|c|)*Real.exp (4*CG*s) < 1) :
    ∀ᶠ T : ℝ in 𝓝[>] 0,
      4*(s/T)*(CG+|c|)*(2*T)*localizedHeatM K (s/T) CG (2*T) ≤ 1 := by
  have hc : ContinuousAt (fun T : ℝ => 8*s*(CG+|c|)*Real.exp (4*(|K| *T+s*CG))) 0 := by fun_prop
  have h0 : 8*s*(CG+|c|)*Real.exp (4*(|K| *0+s*CG)) < 1 := by convert hs using 1; congr 1; ring_nf
  filter_upwards [hc.tendsto.eventually (gt_mem_nhds h0) |>.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with T ht hT
  have hT0 : T ≠ 0 := ne_of_gt hT
  have he : 4*(s/T)*(CG+|c|)*(2*T)*localizedHeatM K (s/T) CG (2*T) =
      8*s*(CG+|c|)*Real.exp (4*(|K| *T+s*CG)) := by
    unfold localizedHeatM
    have harg : 2*(|K|+s/T*CG)*(2*T) = 4*(|K| *T+s*CG) := by field_simp; ring
    rw [harg]; field_simp; ring
  rw [he]; exact ht.le

lemma curvatureTailBound_scaled {K c CG CF s T L C d R S : ℝ} (hT : T ≠ 0) :
    curvatureTailBound K (s/T) c CG (2*T) L (C*Real.exp (2*(s/T)*CF)) d
      (d+(R-S)/(4*T)) R S =
      4*s*(CG+|c|)*L^2*C*Real.exp (4*(|K| *T+s*CG)+2*d^2*T+d*R)*
        Real.exp ((2*s*CF-(R-S)^2/8)/T) := by
  unfold curvatureTailBound localizedHeatM
  have he : 2*(|K|+s/T*CG)*(2*T)+2*(s/T)*CF+
      ((d+(R-S)/(4*T))^2*(2*T)-(d+(R-S)/(4*T))*(R-S)+d*R) =
      4*(|K| *T+s*CG)+2*d^2*T+d*R+(2*s*CF-(R-S)^2/8)/T := by
    field_simp; ring
  have hexp := congrArg Real.exp he
  simp only [Real.exp_add] at hexp
  calc
    _ = (2*(s/T)*(2*T)*(CG+|c|)*L^2*C)*
        (Real.exp (2*(|K|+s/T*CG)*(2*T))*Real.exp (2*(s/T)*CF)*
          Real.exp ((d+(R-S)/(4*T))^2*(2*T)-(d+(R-S)/(4*T))*(R-S)+d*R)) := by ring
    _ = _ := by
      have hp : 2*(s/T)*(2*T) = 4*s := by field_simp; ring
      rw [hp]
      rw [← Real.exp_add,← Real.exp_add,he,Real.exp_add]
      ring

lemma curvatureTailBound_scaling_limit (K c CG CF s L C d R S : ℝ)
    (hgap : 16*s*CF < (R-S)^2) :
    Tendsto (fun T : ℝ => curvatureTailBound K (s/T) c CG (2*T) L
      (C*Real.exp (2*(s/T)*CF)) d (d+(R-S)/(4*T)) R S) (𝓝[>] 0) (𝓝 0) := by
  have hneg : 2*s*CF-(R-S)^2/8 < 0 := by linarith
  have Hexp : Tendsto (fun T : ℝ => Real.exp ((2*s*CF-(R-S)^2/8)/T)) (𝓝[>] 0) (𝓝 0) := by
    have H := Real.tendsto_exp_atBot.comp (tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg hneg)
    simpa only [Function.comp_def,div_eq_mul_inv] using H
  have Hc := (show ContinuousAt (fun T : ℝ => 4*s*(CG+|c|)*L^2*C*
    Real.exp (4*(|K| *T+s*CG)+2*d^2*T+d*R)) 0 from by fun_prop).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have H := Hc.mul Hexp
  simp only [mul_zero] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with T hT
  exact (curvatureTailBound_scaled (ne_of_gt hT)).symm

lemma localActionLimit_slope_limit (c CG : ℝ) :
    Tendsto (fun s : ℝ => (localActionLimit c CG s-1)/s) (𝓝[>] 0) (𝓝 c) := by
  have H := (show ContinuousAt (fun s : ℝ => c+2*|c| *(Real.exp (2*CG*s)-1)+4*c^2*s) 0
    from by fun_prop).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  simp only [mul_zero,Real.exp_zero,sub_self,add_zero] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := ne_of_gt hs
  unfold localActionLimit
  field_simp
  ring

lemma eventually_local_scaling_admissible (c CG CF : ℝ) {g : ℝ} (hg : 0 < g) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      8*s*(CG+|c|)*Real.exp (4*CG*s) < 1 ∧ 16*s*CF < g^2 := by
  have h1 : ContinuousAt (fun s : ℝ => 8*s*(CG+|c|)*Real.exp (4*CG*s)) 0 := by fun_prop
  have h2 : ContinuousAt (fun s : ℝ => 16*s*CF) 0 := by fun_prop
  have H1 := h1.eventually_lt continuousAt_const (by simp : 8*(0:ℝ)*(CG+|c|)*Real.exp (4*CG*0) < 1)
  have H2 := h2.eventually_lt continuousAt_const (by simpa using sq_pos_of_pos hg : 16*(0:ℝ)*CF < g^2)
  exact (H1.and H2).filter_mono nhdsWithin_le_nhds
end WeakHessian

end
end

end OAI
