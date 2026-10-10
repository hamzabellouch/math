import OAI.Analysis.IrrationalRotation.Analysis.RationalGraphTrimming

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem rational_sampling_index {A j r : ℕ}
    (hAa : A ≤ p.blockEnd (j - 1)) (hr : r < p.q A) :
    r * (p.q (p.blockEnd (j - 1)) / p.q A) < p.q (p.blockEnd (j - 1)) ∧
      p.shift j (r * (p.q (p.blockEnd (j - 1)) / p.q A)) = (r : ℝ) / p.q A := by
  let a := p.blockEnd (j - 1)
  have hd : p.q A ∣ p.q a := hp.trimming_frequency_dvd_of_le hAa
  have hmul : p.q A * (p.q a / p.q A) = p.q a := Nat.mul_div_cancel' hd
  have hquot : 0 < p.q a / p.q A := by
    have hqa := hp.q_pos a
    by_contra h
    have hz : p.q a / p.q A = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at hmul
    omega
  constructor
  · calc
      r * (p.q a / p.q A) < p.q A * (p.q a / p.q A) := Nat.mul_lt_mul_of_pos_right hr hquot
      _ = p.q a := hmul
  · have hA0 : (p.q A : ℝ) ≠ 0 := by exact_mod_cast (hp.q_pos A).ne'
    have ha0 : (p.q a : ℝ) ≠ 0 := by exact_mod_cast (hp.q_pos a).ne'
    have hmulR : (p.q A : ℝ) * (p.q a / p.q A : ℕ) = p.q a := by exact_mod_cast hmul
    unfold shift
    change ((r * (p.q a / p.q A) : ℕ) : ℝ) / (p.q a : ℝ) = _
    push_cast
    apply (div_eq_div_iff ha0 hA0).mpr
    nlinarith

theorem rational_selected_time {A j r n : ℕ} (hj : 1 ≤ j)
    (hAa : A ≤ p.blockEnd (j - 1)) (hr : r < p.q A)
    (hn : n ∈ p.samples j (r * (p.q (p.blockEnd (j - 1)) / p.q A))) :
    0 < n ∧ p.Q j / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ p.Q j ∧
      Int.fract ((n : ℝ) * θ - (r : ℝ) / p.q A) ∈ Set.Ioo 0 (p.ell j) := by
  obtain ⟨hindex, hshift⟩ := hp.rational_sampling_index hAa hr
  refine ⟨hp.samples_positive j hj _ hindex n hn,
    (hp.samples_range j hj _ hindex n hn).1,
    (hp.samples_range j hj _ hindex n hn).2, ?_⟩
  simpa only [hshift] using hp.samples_phase j hj _ hindex n hn

theorem eventually_prefix_available (A : ℕ) :
    ∀ᶠ n : ℕ in atTop, A ≤ p.blockEnd n := by
  filter_upwards [eventually_ge_atTop A] with n hn
  exact hn.trans (p.blockEnd_ge_index hp.m_pos n)

theorem ell_le_reciprocal_square (j : ℕ) :
    p.ell j ≤ 1 / ((j + 1 : ℕ) : ℝ)^2 := by
  have ha : 0 ≤ (p.blockEnd (j - 1) : ℝ) := Nat.cast_nonneg _
  have hq : (1 : ℝ) ≤ p.q (p.blockEnd (j - 1)) := by
    exact_mod_cast hp.q_pos (p.blockEnd (j - 1))
  unfold ell
  apply one_div_le_one_div_of_le (by positivity)
  have hfactor : 1 ≤ (1 + (p.blockEnd (j - 1) : ℝ)) *
      (p.q (p.blockEnd (j - 1)) : ℝ) := by
    nlinarith [mul_nonneg ha (Nat.cast_nonneg (p.q (p.blockEnd (j - 1))))]
  calc
    _ ≤ ((j + 1 : ℕ) : ℝ)^2 * ((1 + (p.blockEnd (j - 1) : ℝ)) *
        (p.q (p.blockEnd (j - 1)) : ℝ)) :=
      le_mul_of_one_le_right (sq_nonneg _) hfactor
    _ = _ := by ring

theorem trimming_tendsto_ell_zero : Tendsto (fun n : ℕ => p.ell (n + 1)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_add_atTop_iff_nat 2).mpr tendsto_one_div_atTop_nhds_zero_nat
  have hsq : Tendsto (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div_pow, zero_pow (by decide : 2 ≠ 0)] using h.pow 2
  apply squeeze_zero (fun n => by unfold ell; positivity)
    (fun n => by simpa only [Nat.add_assoc] using hp.ell_le_reciprocal_square (n + 1)) hsq

end Invariant233.CircleParameterLaws

end

end OAI
