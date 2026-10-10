import OAI.Probability.InvariantIsing.Magnetic.ConstrainedBlockMagneticEstimate
import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldParameter
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! The finite block error vanishes uniformly over field partitions with
bounded final height and magnetizations in a fixed interior interval. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

def magneticUniformBiasBound (H r : ℝ) : ℝ := (Real.log 2 + H / 2) / (1 - r)

lemma magneticBias_uniform_bound (h : FieldStep) {H r m : ℝ}
    (hr : r < 1) (hm : |m| ≤ r) (hH : h.height (Fin.last h.depth) ≤ H) :
    |magneticBias h m| ≤ magneticUniformBiasBound H r := by
  have hi := hm.trans_lt hr
  have hb := magneticBias_minimum_bound h hi hH (magneticBias_minimizes h hi)
  have hH0 := (h.nonneg (Fin.last h.depth)).trans hH
  exact hb.trans (div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hr) (by linarith))

lemma normalized_magneticBlockError {N : ℕ} (hN : 0 < N) (C A ε t : ℝ) :
    (N : ℝ)⁻¹ * (ε * (N * C) + (ε⁻¹ + t) * (A * Real.sqrt N) +
      N * Real.log (1 + Real.exp (-t))) =
      ε * C + (ε⁻¹ + t) * A / Real.sqrt N + Real.log (1 + Real.exp (-t)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  field_simp
  linear_combination (ε⁻¹ + t) * A * hs2

lemma log_one_add_exp_neg_tendsto :
    Tendsto (fun t : ℝ => Real.log (1 + Real.exp (-t))) atTop (𝓝 0) := by
  have he := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hh := (tendsto_const_nhds.add he).log (by norm_num : (1 : ℝ) + 0 ≠ 0)
  simpa only [add_zero, Real.log_one, Function.comp_apply] using hh

theorem tendsto_zero_of_magneticBlockError (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (C A : ℝ) (hC : 0 < C)
    (hb : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, 0 ≤ t → ∀ n,
      f n ≤ ε * C + (ε⁻¹ + t) * A / Real.sqrt (N n) + Real.log (1 + Real.exp (-t))) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (hf n))
  · intro a ha
    let ε := a / (4 * C)
    have hε : 0 < ε := div_pos ha (by positivity)
    have hεC : ε * C = a / 4 := by dsimp [ε]; field_simp
    obtain ⟨t, ht, htl⟩ := ((eventually_ge_atTop (0 : ℝ)).and
      (log_one_add_exp_neg_tendsto.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < a / 4)))).exists
    have hi : Tendsto (fun n => (Real.sqrt (N n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN))
    have hm : Tendsto (fun n => (ε⁻¹ + t) * A / Real.sqrt (N n)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul ((ε⁻¹ + t) * A)
    filter_upwards [hm.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < a / 4))] with n hn
    have h := hb ε hε t ht n
    rw [hεC] at h
    linarith

end InvariantIsing

end

end OAI
