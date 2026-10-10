import Mathlib

namespace OAI

section

noncomputable section
open Filter MeasureTheory Finset
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff
variable {X : Type*}

def exceptional (c : ℕ → X → ℝ) : Set X := {x | ¬ Summable (fun n => c n x)}

def saturation (c : ℕ → X → ℝ) (n N : ℕ) (x : X) : ℝ :=
  1 - Real.exp (-(∑ k ∈ Finset.range N, c (k+n) x))

def tailLimit (c : ℕ → X → ℝ) (n : ℕ) (x : X) : ℝ := by
  classical
  exact if Summable (fun k => c k x) then
    1 - Real.exp (-(∑' k, c (k+n) x)) else 1

lemma saturation_nonneg (c : ℕ → X → ℝ) (hc : ∀ n x, 0 ≤ c n x)
    (n N : ℕ) (x : X) : 0 ≤ saturation c n N x := by
  rw [saturation, sub_nonneg, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun k _ => hc (k+n) x))

lemma saturation_le_one (c : ℕ → X → ℝ) (n N : ℕ) (x : X) :
    saturation c n N x ≤ 1 := by
  have := Real.exp_pos (-(∑ k ∈ Finset.range N, c (k+n) x))
  unfold saturation
  linarith

lemma saturation_tendsto_tail (c : ℕ → X → ℝ) (hc : ∀ n x, 0 ≤ c n x)
    (n : ℕ) (x : X) :
    Tendsto (fun N => saturation c n N x) atTop (𝓝 (tailLimit c n x)) := by
  classical
  by_cases hx : Summable (fun k => c k x)
  · simp only [tailLimit,ite_eq_left hx]
    exact tendsto_const_nhds.sub
      (Real.continuous_exp.tendsto _ |>.comp (((summable_nat_add_iff n).2 hx).hasSum.tendsto_sum_nat.neg))
  · simp only [tailLimit,ite_eq_right hx]
    have hns : ¬ Summable (fun k => c (k+n) x) := by
      exact fun h => hx ((summable_nat_add_iff n).1 h)
    have htop := (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun k => hc (k+n) x)).1 hns
    simpa only [sub_zero,saturation,Function.comp_def] using tendsto_const_nhds.sub (Real.tendsto_exp_neg_atTop_nhds_zero.comp htop)

lemma tail_nonneg (c : ℕ → X → ℝ) (hc : ∀ n x, 0 ≤ c n x)
    (n : ℕ) (x : X) : 0 ≤ tailLimit c n x :=
  ge_of_tendsto (saturation_tendsto_tail c hc n x)
    (Eventually.of_forall (fun N => saturation_nonneg c hc n N x))

lemma tail_le_one (c : ℕ → X → ℝ) (hc : ∀ n x, 0 ≤ c n x)
    (n : ℕ) (x : X) : tailLimit c n x ≤ 1 :=
  le_of_tendsto (saturation_tendsto_tail c hc n x)
    (Eventually.of_forall (fun N => saturation_le_one c n N x))

lemma tail_tendsto_indicator (c : ℕ → X → ℝ) (x : X) :
    Tendsto (fun n => tailLimit c n x) atTop
      (𝓝 ((exceptional c).indicator (fun _ => (1:ℝ)) x)) := by
  classical
  by_cases hx : Summable (fun k => c k x)
  · have hxe : x ∉ exceptional c := not_not.mpr hx
    simp only [tailLimit,ite_eq_left hx,Set.indicator_of_notMem hxe]
    simpa only [neg_zero,Real.exp_zero,sub_self,Function.comp_def] using (tendsto_const_nhds (x := (1:ℝ)) (f := atTop)).sub
      (Real.continuous_exp.tendsto _ |>.comp (tendsto_sum_nat_add (fun k => c k x)).neg)
  · have hxe : x ∈ exceptional c := hx
    simp only [tailLimit,ite_eq_right hx,Set.indicator_of_mem hxe]
    exact tendsto_const_nhds

lemma measurable_exceptional [MeasurableSpace X] (c : ℕ → X → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hm : ∀ n, Measurable (c n)) :
    MeasurableSet (exceptional c) := by
  have he : exceptional c = {x | (∑' n, ‖c n x‖ₑ) = ∞} := by
    ext x
    change (¬ Summable (fun n => c n x)) ↔ (∑' n, ‖c n x‖ₑ) = ∞
    have h := (tsum_enorm_ne_top_iff_summable_norm (f := fun n => c n x))
    have hn : (fun n => ‖c n x‖) = (fun n => c n x) := by
      funext n
      exact abs_of_nonneg (hc n x)
    rw [hn] at h
    exact (not_congr h).symm.trans not_not
  rw [he]
  exact measurableSet_eq_fun (Measurable.tsum (fun n => (hm n).enorm)) measurable_const

lemma exceptional_null [MeasurableSpace X] (c : ℕ → X → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hm : ∀ n, Measurable (c n))
    (ν : Measure X) (hs : (∑' n, ∫⁻ x, ENNReal.ofReal (c n x) ∂ν) ≠ ∞) :
    ν (exceptional c) = 0 := by
  have hsum : ∫⁻ x, ∑' n, ‖c n x‖ₑ ∂ν ≠ ∞ := by
    rw [lintegral_tsum (fun n => (hm n).enorm.aemeasurable)]
    simpa only [Real.enorm_eq_ofReal (hc _ _)] using hs
  have hae := ae_lt_top (Measurable.tsum (fun n => (hm n).enorm)) hsum
  change ν {x | ¬ Summable (fun n => c n x)} = 0
  rw [← ae_iff]
  filter_upwards [hae] with x hx
  have := tsum_enorm_ne_top_iff_summable_norm.1 hx.ne
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hc _ x)] using this

lemma measurable_saturation [MeasurableSpace X] (c : ℕ → X → ℝ)
    (hm : ∀ n, Measurable (c n)) (n N : ℕ) : Measurable (saturation c n N) := by
  exact measurable_const.sub (Real.continuous_exp.measurable.comp
    ((Finset.measurable_sum _ (fun k _ => hm (k+n))).neg))

lemma measurable_tail [MeasurableSpace X] (c : ℕ → X → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hm : ∀ n, Measurable (c n)) (n : ℕ) :
    Measurable (tailLimit c n) :=
  measurable_of_tendsto_metrizable (fun N => measurable_saturation c hm n N)
    (tendsto_pi_nhds.mpr (fun x => saturation_tendsto_tail c hc n x))
end TamingCompatibility.SummableCutoff

end
end

end OAI
