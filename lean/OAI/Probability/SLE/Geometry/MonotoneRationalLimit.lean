import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-! A continuous limit on rational times determines the limit at every
time for a sequence of increasing functions. -/

noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge

theorem tendsto_of_monotone_rational_limits
    (A : ℕ → ℝ → ℝ) (a : ℝ → ℝ)
    (hA : ∀ n, Monotone (A n)) (ha : Continuous a)
    (hrat : ∀ q : ℚ, Tendsto (fun n => A n q) atTop (𝓝 (a q)))
    (x : ℝ) : Tendsto (fun n => A n x) atTop (𝓝 (a x)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hn : {y | b < a y} ∈ 𝓝 x :=
      (isOpen_lt continuous_const ha).mem_nhds hb
    obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp hn
    obtain ⟨q,hq,hqx⟩ := exists_rat_btwn (sub_lt_self x hε)
    have hqb : b < a q := he (by
      rw [Metric.mem_ball,Real.dist_eq,abs_of_neg (sub_neg.mpr hqx)]
      linarith)
    filter_upwards [(tendsto_order.mp (hrat q)).1 b hqb] with n hn
    exact hn.trans_le (hA n hqx.le)
  · intro b hb
    have hn : {y | a y < b} ∈ 𝓝 x :=
      (isOpen_lt ha continuous_const).mem_nhds hb
    obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp hn
    obtain ⟨q,hxq,hq⟩ := exists_rat_btwn (lt_add_of_pos_right x hε)
    have hqb : a q < b := he (by
      rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr hxq)]
      linarith)
    filter_upwards [(tendsto_order.mp (hrat q)).2 b hqb] with n hn
    exact (hA n hxq.le).trans_lt hn

end SLEExactGauge

end

end OAI
