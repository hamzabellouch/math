import OAI.NumberTheory.Jacobsthal.Probability.PairedDrift

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedBlockContraction

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open TransitionKernels PairedHitting PairedDrift

theorem moment_add_constant (n : ℕ) (s : OddState) {D : ℝ} (hD : 0 ≤ D) :
    (∫⁻ t, ENNReal.ofReal (V t + D) ∂(pairedKilled ^ n) s) =
      (∫⁻ t, ENNReal.ofReal (V t) ∂(pairedKilled ^ n) s) +
        ENNReal.ofReal D * (pairedKilled ^ n) s univ := by
  have heq : ∀ t : OddState, ENNReal.ofReal (V t + D) = ENNReal.ofReal (V t) + ENNReal.ofReal D :=
    fun t => ENNReal.ofReal_add (V_pos t).le hD
  rw [lintegral_congr heq, lintegral_add_left (f := fun t : OddState => ENNReal.ofReal (V t)) (ENNReal.measurable_ofReal.comp V_measurable) (fun _ => ENNReal.ofReal D), lintegral_const]

theorem actual_block_contraction : ∃ m : ℕ, 0 < m ∧ ∃ ρ D : ℝ,
    0 < ρ ∧ ρ < 1 ∧ 0 < D ∧ ∀ s : OddState,
      (∫⁻ t, ENNReal.ofReal (V t + D) ∂(pairedKilled ^ m) s) ≤
        ENNReal.ofReal (ρ * (V s + D)) := by
  obtain ⟨a, B, ha, ha1, hB, hDrift⟩ := pairedKilled_iterated_drift
  let M := max 4 (8 * B)
  have hM : 4 ≤ M := le_max_left _ _
  obtain ⟨m0, hm0, p, hp, hp1, hHit⟩ := compact_paired_survival hM
  have hpow : Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha.le ha1
  have hsmall : ∀ᶠ n in atTop, a ^ n < 1 / 4 := (tendsto_order.mp hpow).2 _ (by norm_num)
  obtain ⟨m, hma, hm⟩ := (hsmall.and (eventually_ge_atTop m0)).exists
  let D := 2 * B / p
  let ρ := 1 - p / 2
  have hD : 0 < D := div_pos (by linarith) hp
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  refine ⟨m, lt_of_lt_of_le hm0 hm, ρ, D, hρ, hρ1, hD, ?_⟩
  intro s
  rw [moment_add_constant m s hD.le]
  have hE : 0 ≤ a ^ m * V s + B := add_nonneg (mul_nonneg (pow_nonneg ha.le _) (V_pos s).le) hB.le
  by_cases hs : s.1 ≤ M
  · calc
      _ ≤ ENNReal.ofReal (a ^ m * V s + B) + ENNReal.ofReal D * ENNReal.ofReal (1 - p) :=
        add_le_add (hDrift m s) (mul_le_mul le_rfl (hHit m hm s hs) zero_le zero_le)
      _ = ENNReal.ofReal (a ^ m * V s + B + D * (1 - p)) := by
        rw [← ENNReal.ofReal_mul hD.le, ← ENNReal.ofReal_add hE (mul_nonneg hD.le (by linarith))]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (block_drift_algebra hma.le hB.le hp hp1 (V_pos s).le
        (le_refl _) (show 1 - p ≤ 1 by linarith) (Or.inl le_rfl))
  · have hlarge : 8 * B ≤ V s := by
      dsimp [V]
      have hMb : 8 * B ≤ M := le_max_right _ _
      linarith [Real.add_one_le_exp s.1]
    calc
      _ ≤ ENNReal.ofReal (a ^ m * V s + B) + ENNReal.ofReal D := by
        apply add_le_add (hDrift m s)
        simpa only [mul_one] using mul_le_mul (le_refl (ENNReal.ofReal D)) (paired_survival_le_one m s) zero_le zero_le
      _ = ENNReal.ofReal (a ^ m * V s + B + D) := (ENNReal.ofReal_add hE hD.le).symm
      _ ≤ _ := by
        have h := block_drift_algebra hma.le hB.le hp hp1 (V_pos s).le (le_refl _) (le_refl (1 : ℝ)) (Or.inr hlarge)
        simpa only [mul_one] using ENNReal.ofReal_le_ofReal h

theorem paired_survival_geometric : ∃ m : ℕ, 0 < m ∧ ∃ ρ D : ℝ,
    0 < ρ ∧ ρ < 1 ∧ 0 < D ∧ ∀ n : ℕ, ∀ s : OddState,
      (pairedKilled ^ (m * n)) s univ ≤ ENNReal.ofReal (ρ ^ n * (V s + D)) := by
  obtain ⟨m, hm, ρ, D, hρ, hρ1, hD, hblock⟩ := actual_block_contraction
  have hW : Measurable (fun s : OddState => ENNReal.ofReal (V s + D)) :=
    ENNReal.measurable_ofReal.comp (V_measurable.add measurable_const)
  have hIter : ∀ n : ℕ, ∀ s : OddState,
      (∫⁻ t, ENNReal.ofReal (V t + D) ∂(pairedKilled ^ (m * n)) s) ≤
        ENNReal.ofReal (ρ ^ n * (V s + D)) := by
    intro n
    induction n with
    | zero =>
      intro s
      change (∫⁻ t, ENNReal.ofReal (V t + D) ∂Measure.dirac s) ≤ _
      rw [lintegral_dirac' s hW]
      simp
    | succ n ih =>
      intro s
      have hp : pairedKilled ^ (m * (n + 1)) = (pairedKilled ^ m) ∘ₖ (pairedKilled ^ (m * n)) := by
        rw [show m * (n + 1) = m + m * n by ring, Kernel.pow_add]
      rw [hp, Kernel.lintegral_comp _ _ _ hW]
      calc
        _ ≤ ∫⁻ t, ENNReal.ofReal ρ * ENNReal.ofReal (V t + D) ∂(pairedKilled ^ (m * n)) s := by
          apply lintegral_mono
          intro t
          simpa only [ENNReal.ofReal_mul hρ.le] using hblock t
        _ = ENNReal.ofReal ρ * (∫⁻ t, ENNReal.ofReal (V t + D) ∂(pairedKilled ^ (m * n)) s) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal ρ * ENNReal.ofReal (ρ ^ n * (V s + D)) := mul_le_mul le_rfl (ih s) zero_le zero_le
        _ = _ := by rw [← ENNReal.ofReal_mul hρ.le, pow_succ]; congr 1; ring
  refine ⟨m, hm, ρ, D, hρ, hρ1, hD, ?_⟩
  intro n s
  calc
    _ = ∫⁻ _t, (1 : ℝ≥0∞) ∂(pairedKilled ^ (m * n)) s := by simp
    _ ≤ ∫⁻ t, ENNReal.ofReal (V t + D) ∂(pairedKilled ^ (m * n)) s := lintegral_mono (fun t =>
      by exact (ENNReal.one_le_ofReal).mpr (by linarith [V_one_le t]))
    _ ≤ _ := hIter n s

theorem paired_survival_tendsto_zero (s : OddState) :
    Tendsto (fun n => (pairedKilled ^ n) s univ) atTop (𝓝 0) := by
  obtain ⟨m, hm, ρ, D, hρ, hρ1, hD, hb⟩ := paired_survival_geometric
  have hdiv : Tendsto (fun n : ℕ => n / m) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨m * b, fun n hn => (Nat.le_div_iff_mul_le hm).mpr (by simpa [Nat.mul_comm] using hn)⟩
  have hreal : Tendsto (fun n : ℕ => ρ ^ (n / m) * (V s + D)) atTop (𝓝 0) := by
    simpa only [zero_mul, Function.comp_apply] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).comp hdiv).mul_const (V s + D)
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (ρ ^ (n / m) * (V s + D))) atTop (𝓝 0) := by
    convert! ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal using 1
    simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => show (0 : ℝ≥0∞) ≤ _ from zero_le))
  apply Eventually.of_forall
  intro n
  exact le_trans (paired_survival_antitone s (Nat.mul_div_le n m)) (hb (n / m) s)

end NumberTheoryLean.PairedBlockContraction

end

end Erdos970

end OAI
