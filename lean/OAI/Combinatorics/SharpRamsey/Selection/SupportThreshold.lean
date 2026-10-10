import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.EndpointSupports

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section

lemma log_entropy_envelope {x A h : ℝ} (hx : 1≤x) (hA : 0≤A)
    (hh : 0≤h) (hcap : h≤A*x) :
    log (h+2) ≤ log (A+2)+log x := by
  have hx0 : 0<x := by linarith
  have hA0 : 0<A+2 := by linarith
  rw [←log_mul hA0.ne' hx0.ne']
  apply log_le_log (by linarith)
  nlinarith

def supportErrorEnvelope (b C C₀ A x : ℝ) : ℝ :=
  (2+100*exp 1)*x^(-2*b)+
  (2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀)/x^(4*b)+
  4*log x/x^(4*b)+2*exp 1*exp (-(x^(4*b)))

lemma supportErrorEnvelope_tendsto (b C C₀ A : ℝ) (hb : 0<b) :
    Tendsto (supportErrorEnvelope b C C₀ A) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun x : ℝ => (2+100*exp 1)*x^(-2*b)) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_mul] using
      (tendsto_rpow_neg_atTop (show 0<2*b by positivity)).const_mul (2+100*exp 1)
  have h₂ : Tendsto (fun x : ℝ =>
      (2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀)/x^(4*b)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0<4*b by positivity)).const_mul
      (2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀)
    simp only [mul_zero] at h
    apply (h.congr' ?_)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    simp only [Real.rpow_neg hx, div_eq_mul_inv]
  have h₃ : Tendsto (fun x : ℝ => 4*log x/x^(4*b)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      ((isLittleO_log_rpow_atTop (show 0<4*b by positivity)).tendsto_div_nhds_zero).const_mul 4
  have h₄ : Tendsto (fun x : ℝ => 2*exp 1*exp (-(x^(4*b)))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_rpow_atTop (show 0<4*b by positivity)))
    simpa only [Function.comp_def, mul_zero] using h.const_mul (2*exp 1)
  unfold supportErrorEnvelope
  simpa only [add_zero] using ((h₁.add h₂).add h₃).add h₄

theorem eventually_support_small (b C C₀ A : ℝ) (hb : 0<b)
    (hC : 1≤C) (hC₀ : 0≤C₀) (hA : 0≤A) :
    ∀ᶠ x : ℝ in atTop, ∀ κ δ H HA HB L S : ℝ,
      x^(4*b)≤κ → δ≤κ*x^(-2*b) → L-H≤δ → S*exp (-L)≤C₀ →
      0≤HA → HA≤A*x → 0≤HB → HB≤A*x →
      (2*(log (2*C)+L-H+log (HA+2)+log (HB+2)+2))/κ+
        2*exp 1*(exp (-κ)+(L-H+S*exp (-L))/(κ*(1/50))) ≤ 1/2 := by
  filter_upwards [(supportErrorEnvelope_tendsto b C C₀ A hb).eventually
      (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)), eventually_ge_atTop (1:ℝ)] with x he hx
  intro κ δ H HA HB L S hκ hδ hH hS hHA0 hHA hHB0 hHB
  have hx0 : 0<x := by linarith
  have hxpow : 0<x^(4*b) := rpow_pos_of_pos hx0 _
  have hκ0 : 0<κ := hxpow.trans_le hκ
  have hlA := log_entropy_envelope hx hA hHA0 hHA
  have hlB := log_entropy_envelope hx hA hHB0 hHB
  have hlogx : 0≤log x := log_nonneg hx
  have hlogC : 0≤log (2*C) := log_nonneg (by linarith)
  have hlogA : 0≤log (A+2) := log_nonneg (by linarith)
  have hdiv : δ/κ≤x^(-2*b) := (div_le_iff₀ hκ0).mpr (by simpa only [mul_comm κ] using hδ)
  have hconst0 : 0≤2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀ := by positivity
  have hconst := div_le_div_of_nonneg_left hconst0 hxpow hκ
  have hlog := div_le_div_of_nonneg_left (show 0≤4*log x by positivity) hxpow hκ
  have hexp : exp (-κ)≤exp (-(x^(4*b))) := exp_le_exp.mpr (neg_le_neg hκ)
  have hfirst : (2*(log (2*C)+L-H+log (HA+2)+log (HB+2)+2))/κ ≤
      (2*(log (2*C)+δ+2*(log (A+2)+log x)+2))/κ := by
    apply div_le_div_of_nonneg_right _ hκ0.le
    linarith
  have hsecond : 2*exp 1*(exp (-κ)+(L-H+S*exp (-L))/(κ*(1/50))) ≤
      2*exp 1*(exp (-κ)+(δ+C₀)/(κ*(1/50))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add_right
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hsplit : (2*(log (2*C)+δ+2*(log (A+2)+log x)+2))/κ+
      2*exp 1*(exp (-κ)+(δ+C₀)/(κ*(1/50))) =
      (2+100*exp 1)*(δ/κ)+
      (2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀)/κ+
      4*log x/κ+2*exp 1*exp (-κ) := by ring
  apply (add_le_add hfirst hsecond).trans
  rw [hsplit]
  apply le_trans _ he.le
  unfold supportErrorEnvelope
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hdiv (by positivity)) hconst) hlog)
      (mul_le_mul_of_nonneg_left hexp (by positivity))

end
end SharpLogRamsey.Selection

end

end OAI
