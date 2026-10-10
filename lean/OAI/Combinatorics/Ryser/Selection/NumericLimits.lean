import OAI.Combinatorics.Ryser.Selection.AnalyticalLimits
import Mathlib.Tactic.NormNum

namespace OAI

open Filter Topology

namespace RyserCoveringCounterexample.Selection

theorem tendsto_small_selection_term (K R : ℕ) (A C : ℝ) (hK : 3 < K) :
    Tendsto (fun q : ℕ => (R : ℝ) * A *
      (2 * C * (R : ℝ) / (q : ℝ)) ^ (K - 3)) atTop (𝓝 0) := by
  have hm : K - 3 ≠ 0 := (Nat.sub_pos_of_lt hK).ne'
  have hratio : Tendsto (fun q : ℕ => 2 * C * (R : ℝ) / (q : ℝ))
      atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop (2 * C * (R : ℝ))
  simpa only [zero_pow hm, mul_zero] using
    (hratio.pow (K - 3)).const_mul ((R : ℝ) * A)

theorem tendsto_density_selection_term (D : ℕ) (J B c : ℝ)
    (hB : 0 < B) (hc : 0 < c) :
    Tendsto (fun q : ℕ => J * ((D : ℝ) * (q : ℝ)) * B ^ (D * q) *
      Real.exp (-c * (q : ℝ) * Real.log (q : ℝ))) atTop (𝓝 0) := by
  have hlimit : Tendsto (fun q : ℕ => (J * (D : ℝ)) * ((q : ℝ) *
      Real.exp (((D : ℝ) * Real.log B) * (q : ℝ) -
        c * (q : ℝ) * Real.log (q : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_nat_mul_exp_linear_sub_mul_log hc ((D : ℝ) * Real.log B)).const_mul
        (J * (D : ℝ))
  apply hlimit.congr
  intro q
  have hpow : B ^ (D * q) = Real.exp ((D : ℝ) * (q : ℝ) * Real.log B) := by
    rw [← Nat.cast_mul, Real.exp_nat_mul, Real.exp_log hB]
  have harg : ((D : ℝ) * Real.log B) * (q : ℝ) - c * (q : ℝ) * Real.log (q : ℝ) =
      (D : ℝ) * (q : ℝ) * Real.log B + (-c * (q : ℝ) * Real.log (q : ℝ)) := by ring
  rw [hpow, harg, Real.exp_add]
  ring

theorem tendsto_half_pow_nat_floor_mul {c1 : ℝ} (hc1 : 0 < c1) :
    Tendsto (fun q : ℕ => (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ)))
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [Function.comp_def] using
    hpow.comp (tendsto_nat_floor_mul_atTop c1 hc1)

noncomputable def selectionFailureBound (D K R : ℕ) (A B C J c c1 : ℝ) (q : ℕ) : ℝ :=
  (R : ℝ) * A * (2 * C * (R : ℝ) / (q : ℝ)) ^ (K - 3) + (1 / 2 : ℝ) ^ R +
    J * ((D : ℝ) * (q : ℝ)) * B ^ (D * q) *
      Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
    (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ))

theorem tendsto_selectionFailureBound (D K R : ℕ) (A B C J c c1 : ℝ)
    (hK : 3 < K) (hB : 0 < B) (hc : 0 < c) (hc1 : 0 < c1) :
    Tendsto (selectionFailureBound D K R A B C J c c1) atTop
      (𝓝 ((1 / 2 : ℝ) ^ R)) := by
  change Tendsto
    (fun q : ℕ =>
      (R : ℝ) * A * (2 * C * (R : ℝ) / (q : ℝ)) ^ (K - 3) + (1 / 2 : ℝ) ^ R +
        J * ((D : ℝ) * (q : ℝ)) * B ^ (D * q) *
          Real.exp (-c * (q : ℝ) * Real.log (q : ℝ)) +
        (1 / 2 : ℝ) ^ Nat.floor (c1 * (q : ℝ)))
    atTop (𝓝 ((1 / 2 : ℝ) ^ R))
  simpa only [zero_add, add_zero] using
    (((tendsto_small_selection_term K R A C hK).add_const ((1 / 2 : ℝ) ^ R)).add
      (tendsto_density_selection_term D J B c hB hc)).add
        (tendsto_half_pow_nat_floor_mul hc1)

theorem exists_cutoff_threshold_selectionFailureBound (D K : ℕ) (A B C J c c1 : ℝ)
    (hK : 3 < K) (hB : 0 < B) (hc : 0 < c) (hc1 : 0 < c1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, 1 ≤ R ∧ ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      selectionFailureBound D K R A B C J c c1 q < ε := by
  have hpow : Tendsto (fun R : ℕ => (1 / 2 : ℝ) ^ R) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ R : ℕ in atTop, (1 / 2 : ℝ) ^ R < ε :=
    hpow.eventually (gt_mem_nhds hε)
  obtain ⟨R, hRge, hRsmall⟩ := ((eventually_ge_atTop (1 : ℕ)).and hsmall).exists
  have hbound : ∀ᶠ q : ℕ in atTop,
      selectionFailureBound D K R A B C J c c1 q < ε :=
    (tendsto_selectionFailureBound D K R A B C J c c1 hK hB hc hc1).eventually
      (gt_mem_nhds hRsmall)
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 hbound
  exact ⟨R, hRge, Q, hQ⟩

end RyserCoveringCounterexample.Selection

end OAI
