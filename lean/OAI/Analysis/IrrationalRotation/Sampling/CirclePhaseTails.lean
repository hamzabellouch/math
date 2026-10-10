import OAI.Analysis.IrrationalRotation.Sampling.CirclePhaseSummability

namespace OAI

noncomputable section
open Filter
open scoped BigOperators Topology

namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem block_phase_tail_bound (j : ℕ) (hj : 1 ≤ j) :
    (∑' n : ℕ, ∑ i ∈ p.block (j + 1 + n), p.alpha θ i) ≤
      4 / (p.K (j + 1) : ℝ) := by
  have hs : Summable (fun n : ℕ =>
      ∑ i ∈ p.block (j + 1 + n), p.alpha θ i) := by
    have h := (summable_nat_add_iff j).mpr hp.summable_block_phases
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hK : Summable (fun n : ℕ => 1 / (p.K (j + 1 + n) : ℝ)) := by
    have h := (summable_nat_add_iff j).mpr hp.summable_reciprocal
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  calc
    _ ≤ ∑' n : ℕ, 2 * (1 / (p.K (j + 1 + n) : ℝ)) := by
      apply Summable.tsum_le_tsum _ hs (hK.mul_left 2)
      intro n
      simpa only [mul_one_div] using hp.block_phase_sum_le (j + 1 + n) (by omega)
    _ = 2 * ∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ) := tsum_mul_left
    _ ≤ 2 * (2 / (p.K (j + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hp.reciprocal_tail_bound j hj) (by norm_num)
    _ = _ := by ring

theorem sampled_phase_tail_bound (j r n : ℕ) (hj : 1 ≤ j)
    (hr : r < p.q (p.blockEnd (j - 1))) (hn : n ∈ p.samples j r) :
    (n : ℝ) * (∑' s : ℕ, ∑ i ∈ p.block (j + 1 + s), p.alpha θ i) ≤
      4 * p.Q j / (p.K (j + 1) : ℝ) := by
  have hK : 0 < (p.K (j + 1) : ℝ) := by
    exact_mod_cast hp.K_pos (j + 1) (by omega)
  calc
    _ ≤ (n : ℝ) * (4 / (p.K (j + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hp.block_phase_tail_bound j hj) (Nat.cast_nonneg n)
    _ ≤ p.Q j * (4 / (p.K (j + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_right (hp.samples_range j hj r hr n hn).2 (by positivity)
    _ = _ := by ring

theorem early_trimming_bound (j : ℕ) :
    (p.blockEnd (j - 1) : ℝ) * (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j ≤
      1 / ((j + 1 : ℕ) : ℝ)^2 := by
  have hq : 0 < (p.q (p.blockEnd (j - 1)) : ℝ) := by
    exact_mod_cast hp.q_pos (p.blockEnd (j - 1))
  have ha : 0 ≤ (p.blockEnd (j - 1) : ℝ) := Nat.cast_nonneg _
  have hr : (p.blockEnd (j - 1) : ℝ) / (1 + (p.blockEnd (j - 1) : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  calc
    _ = ((p.blockEnd (j - 1) : ℝ) / (1 + (p.blockEnd (j - 1) : ℝ))) *
        (1 / ((j + 1 : ℕ) : ℝ)^2) := by
      unfold CircleParameterData.ell
      field_simp
    _ ≤ 1 * (1 / ((j + 1 : ℕ) : ℝ)^2) :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := one_mul _

theorem discarded_mass_bound (j : ℕ) (hj : 1 ≤ j) :
    (p.blockEnd (j - 1) : ℝ) * (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j +
      2 * p.Q j * (∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ)) ≤
      1 / ((j + 1 : ℕ) : ℝ)^2 + 4 * p.Q j / (p.K (j + 1) : ℝ) := by
  apply add_le_add (hp.early_trimming_bound j)
  have hQ : 0 ≤ p.Q j := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ ≤ 2 * p.Q j * (2 / (p.K (j + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hp.reciprocal_tail_bound j hj) (by positivity)
    _ = _ := by ring

theorem tendsto_discarded_mass_bound :
    Tendsto (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)^2 +
      4 * p.Q (n + 1) / (p.K (n + 2) : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    exact (tendsto_add_atTop_iff_nat 2).mpr tendsto_one_div_atTop_nhds_zero_nat
  have hsq : Tendsto (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)^2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div_pow, zero_pow (by decide : 2 ≠ 0)] using h.pow 2
  have hg := hsq.add (hp.tendsto_sampling_horizon.const_mul 4)
  simpa only [mul_div_assoc, zero_add, mul_zero] using hg

end Invariant233.CircleParameterLaws

end

end OAI
