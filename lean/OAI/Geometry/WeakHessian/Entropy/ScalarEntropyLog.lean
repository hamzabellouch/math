import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.AddConst

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile2
noncomputable section
namespace WeakHessianEntropyScalar

lemma log_floor_difference_mono {a b u v : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.log (u+b)-Real.log (u+a) ≤ Real.log (v+b)-Real.log (v+a) := by
  have ha : 0 < a := hb.trans_le hba
  have hv : 0 ≤ v := hu.trans huv
  rw [← Real.log_div (by positivity) (by positivity),
    ← Real.log_div (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr huv)]

lemma log_floor_comparison_good {a b d u v : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hd : 0 ≤ d) (hu : 0 < u) (hu2 : 2*d ≤ u) (hvu : u-d ≤ v) :
    u^2*(Real.log (v+b)-Real.log (u+b)-Real.log (v+a)+Real.log (u+a)) ≥ -2*a*d := by
  have ha : 0 < a := hb.trans_le hba
  have hv : 0 < v := by linarith
  by_cases huv : u ≤ v
  · have H := log_floor_difference_mono hb hba hu.le huv
    have J : 0 ≤ u^2*(Real.log (v+b)-Real.log (u+b)-Real.log (v+a)+Real.log (u+a)) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith [mul_nonneg ha.le hd]
  have hvu' : v ≤ u := le_of_not_ge huv
  let E := (u+a)*(v+b)
  have hE : 0 < E := by dsimp [E]; positivity
  have hE2 : u^2 ≤ 2*E := by
    have H : u^2 ≤ 2*(u*v) := by nlinarith
    have J : u*v ≤ E := by dsimp [E]; nlinarith [mul_nonneg hu.le hb.le,mul_nonneg ha.le hv.le,mul_nonneg ha.le hb.le]
    linarith
  have hn : (a-b)*(u-v) ≤ a*d := by
    calc
      _ ≤ a*(u-v) := by gcongr; linarith
      _ ≤ a*d := by gcongr; linarith
  have heq : (u+b)*(v+a)/E-1 = (a-b)*(u-v)/E := by
    dsimp only [E]
    field_simp
    ring
  have hR : 0 < (u+b)*(v+a)/E := by positivity
  have hlog := Real.log_le_sub_one_of_pos hR
  rw [Real.log_div (by positivity) hE.ne',Real.log_mul (by positivity) (by positivity),
    show Real.log E = Real.log (u+a)+Real.log (v+b) by
      dsimp [E]; rw [Real.log_mul (by positivity) (by positivity)],heq] at hlog
  have H : u^2*((a-b)*(u-v)/E) ≤ 2*a*d := by
    rw [← mul_div_assoc,div_le_iff₀ hE]
    calc
      u^2*((a-b)*(u-v)) ≤ u^2*(a*d) := mul_le_mul_of_nonneg_left hn (sq_nonneg _)
      _ ≤ (2*E)*(a*d) := mul_le_mul_of_nonneg_right hE2 (mul_nonneg ha.le hd)
      _ = 2*a*d*E := by ring
  have J := mul_le_mul_of_nonneg_left hlog (sq_nonneg u)
  nlinarith

lemma log_floor_comparison {a b d u v : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hd : 0 ≤ d) (hu : 0 ≤ u) (hv : 0 ≤ v) (hvu : u-d ≤ v) :
    u^2*(Real.log (v+b)-Real.log (u+b)-Real.log (v+a)+Real.log (u+a)) ≥
      -2*a*d-4*d^2*Real.log ((2*d+b)/b) := by
  have ha : 0 < a := hb.trans_le hba
  have hr : 1 ≤ (2*d+b)/b := by rw [le_div_iff₀ hb]; linarith
  have hl := Real.log_nonneg hr
  by_cases hu2 : 2*d ≤ u
  · by_cases hu0 : u = 0
    · subst u
      have hd0 : d = 0 := by linarith
      simp [hd0]
    · have H := log_floor_comparison_good hb hba hd (lt_of_le_of_ne hu (Ne.symm hu0)) hu2 hvu
      nlinarith [mul_nonneg (sq_nonneg d) hl]
  have hu2' : u ≤ 2*d := le_of_not_ge hu2
  have H := log_floor_difference_mono hb hba (by norm_num : (0:ℝ) ≤ 0) hv
  simp only [zero_add] at H
  have J := Real.log_le_log ha (show a ≤ u+a by linarith)
  have I := Real.log_le_log (show 0 < u+b by positivity) (show u+b ≤ 2*d+b by linarith)
  have B : -(Real.log ((2*d+b)/b)) ≤
      Real.log (v+b)-Real.log (u+b)-Real.log (v+a)+Real.log (u+a) := by
    rw [Real.log_div (by positivity) hb.ne']
    linarith
  have han : 0 ≤ 2*a*d := by positivity
  have H1 := mul_le_mul_of_nonneg_left B (sq_nonneg u)
  have H2 : u^2*Real.log ((2*d+b)/b) ≤ 4*d^2*Real.log ((2*d+b)/b) := by
    gcongr
    nlinarith
  nlinarith
open Filter Set
open scoped Topology

lemma tendsto_time_log_reciprocal {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun t : ℝ => t*Real.log (1+c/t)) (𝓝[>] 0) (𝓝 0) := by
  rcases hc.eq_or_lt with h|h
  · subst c
    simp
  have H : Tendsto (fun t : ℝ => t*Real.log (t+c)) (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using ht.mul ((Real.continuousAt_log h.ne').tendsto.comp
      (by simpa using ht.add_const c))
  have J : Tendsto (fun t : ℝ => t*Real.log t) (𝓝[>] 0) (𝓝 0) := by
    simpa using Real.continuous_mul_log.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  convert (H.sub J).congr' ?_ using 1
  · norm_num
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have heq : 1+c/t = (t+c)/t := by field_simp
    rw [heq,Real.log_div (by positivity) ht.ne']
    ring

end WeakHessianEntropyScalar

end
end InlinedFile2

end OAI
