import Mathlib

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Filter

structure PartitionParameters (δ : ℝ) where
  D : ℕ
  t : ℕ
  ε : ℚ
  D_ge : 2 ≤ D
  t_pos : 1 ≤ t
  ε_pos : 0 < ε
  margin : 1 - (1 - 1 / (D : ℝ)) ^ D + (D : ℝ) / t +
    (t : ℝ)^2 * (D : ℝ)^2 * (ε : ℝ) < 1 - 1 / Real.exp 1 + δ

theorem partition_parameters_exist {δ : ℝ} (hδ : 0 < δ) :
    Nonempty (PartitionParameters δ) := by
  have hlim : Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ)) ^ n) atTop
      (nhds (1 / Real.exp 1)) := by
    simpa only [neg_div, one_div, sub_eq_add_neg, Real.exp_neg] using
      Real.tendsto_one_add_div_pow_exp (-1)
  have hev : ∀ᶠ n : ℕ in atTop,
      1 / Real.exp 1 - δ / 3 < (1 - 1 / (n : ℝ)) ^ n :=
    hlim.eventually_const_lt (by linarith)
  obtain ⟨D,hD,hd⟩ := ((eventually_ge_atTop 2).and hev).exists
  have hDr : 0 < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  obtain ⟨t,ht⟩ := exists_nat_gt ((D : ℝ) / (δ / 3))
  have ht0 : 0 < (t : ℝ) := lt_trans (div_pos hDr (by linarith)) ht
  have htp : 1 ≤ t := by exact_mod_cast (show (1 : ℝ) ≤ t by
    have : 0 < t := by exact_mod_cast ht0
    exact_mod_cast this)
  have hratio : (D : ℝ) / t < δ / 3 := by
    apply (div_lt_iff₀ ht0).mpr
    have := (div_lt_iff₀ (by linarith : 0 < δ / 3)).mp ht
    nlinarith
  have hden : 0 < (t : ℝ)^2 * (D : ℝ)^2 := mul_pos (sq_pos_of_pos ht0) (sq_pos_of_pos hDr)
  obtain ⟨ε,hε,he⟩ := exists_rat_btwn (div_pos (show 0 < δ / 3 by linarith) hden)
  have hsmall : (t : ℝ)^2 * (D : ℝ)^2 * (ε : ℝ) < δ / 3 := by
    have := (lt_div_iff₀ hden).mp he
    nlinarith
  refine ⟨⟨D,t,ε,hD,htp,?_,?_⟩⟩
  · exact_mod_cast hε
  · linarith

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
