import OAI.Analysis.IrrationalRotation.Sampling.CharacterSamplingStage

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Invariant233.TrialSampling

theorem exists_realized_block_of_moment_budget {θ : ℝ} (hθ : Irrational θ)
    (m j : ℕ) (hm : 200 ≤ m) (hj : 0 < j) {N : ℝ} (hN : 2 < N)
    (r : ℕ) (samples : Fin r → Finset ℕ)
    (hpositive : ∀ k, ∀ n ∈ samples k, 0 < n)
    {δ : ℝ≥0∞}
    (hmoment : ∀ k endpoint,
      (∫⁻ phase, squaredError m (samples k) endpoint phase ∂phaseLaw m N) ≤ δ)
    (hbudget : ENNReal.ofReal (ProductPhases.failureBound m) +
      (2 * r : ℝ≥0∞) * (δ / ENNReal.ofReal ((1 / (2 * (j : ℝ))) ^ 2)) < 1)
    {q₀ : ℕ} (hq₀ : 0 < q₀) (R : ℝ) :
    ∃ q : ℕ → ℕ,
      q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
      (∀ i, q i ∣ q (i + 1)) ∧
      (∀ i < m, R ≤ (q (i + 1) : ℝ) / (q i : ℝ)) ∧
      (∀ i : Fin m, Int.fract ((q (i.val + 1) : ℝ) * θ) ∈ Ioo (1 / N) (2 / N)) ∧
      ProductPhases.strictLargePhaseCondition Finset.univ N
        (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)) ∧
      ∀ k endpoint,
        eLpNorm (fun x : Circle => average m (samples k) endpoint
          (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
          (fun i : Fin m => (q (i.val + 1) : ℤ) • x) - 1) 2 circleMeasure <
            ENNReal.ofReal (1 / (j : ℝ)) := by
  have hsmallpos : 0 < 1 / (2 * (j : ℝ)) := by positivity
  obtain ⟨q, hzero, hpos, hmono, hdiv, hratio, hbox, hspread, hnorm⟩ :=
    SamplingTests.exists_character_stage_of_moment_budget hθ hm hN samples hpositive
      hsmallpos hmoment (by simpa only [Fintype.card_fin] using hbudget) R hq₀
  refine ⟨q, hzero, hpos, hmono, hdiv, hratio, hbox, hspread, ?_⟩
  intro k endpoint
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hsmall : 1 / (2 * (j : ℝ)) < 1 / (j : ℝ) := by
    apply one_div_lt_one_div_of_lt hjR
    linarith
  exact (hnorm k endpoint).trans
    ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hsmall)

theorem eventually_exists_realized_block_of_moments_tendsto_zero
    {θ : ℝ} (hθ : Irrational θ) (j : ℕ) (hj : 0 < j)
    (N : ℕ → ℝ) (hN : ∀ᶠ m in atTop, 2 < N m)
    (r : ℕ) (samples : (m : ℕ) → Fin r → Finset ℕ)
    (hpositive : ∀ᶠ m in atTop, ∀ k, ∀ n ∈ samples m k, 0 < n)
    (hmoment : ∀ k endpoint,
      Tendsto (fun m => ∫⁻ phase, squaredError m (samples m k) endpoint phase
        ∂phaseLaw m (N m)) atTop (𝓝 0)) :
    ∀ᶠ m in atTop, ∀ (R : ℝ) (q₀ : ℕ), 0 < q₀ →
      ∃ q : ℕ → ℕ,
        q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
        (∀ i, q i ∣ q (i + 1)) ∧
        (∀ i < m, R ≤ (q (i + 1) : ℝ) / (q i : ℝ)) ∧
        (∀ i : Fin m, Int.fract ((q (i.val + 1) : ℝ) * θ) ∈
          Ioo (1 / N m) (2 / N m)) ∧
        ProductPhases.strictLargePhaseCondition Finset.univ (N m)
          (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)) ∧
        ∀ k endpoint,
          eLpNorm (fun x : Circle => average m (samples m k) endpoint
            (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
            (fun i : Fin m => (q (i.val + 1) : ℤ) • x) - 1) 2 circleMeasure <
              ENNReal.ofReal (1 / (j : ℝ)) := by
  classical
  let δ : ℕ → ℝ≥0∞ := fun m => ∑ t : Fin r × Bool,
    ∫⁻ phase, squaredError m (samples m t.1) t.2 phase ∂phaseLaw m (N m)
  let ε : ℝ≥0∞ := ENNReal.ofReal ((1 / (2 * (j : ℝ))) ^ 2)
  have hε0 : ε ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos (by positivity))
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hh := tendsto_finsetSum (Finset.univ : Finset (Fin r × Bool))
      (fun t _ => hmoment t.1 t.2)
    simpa only [Finset.sum_const_zero] using hh
  have hdiv : Tendsto (fun m => δ m / ε) atTop (𝓝 0) := by
    simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hδ (Or.inr hε0)
  have hmul : Tendsto (fun m => (2 * r : ℝ≥0∞) * (δ m / ε)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul (a := (2 * r : ℝ≥0∞)) hdiv
        (Or.inr (by finiteness)))
  have hbudget : ∀ᶠ (m : ℕ) in atTop,
      ENNReal.ofReal (ProductPhases.failureBound m) +
        (2 * r : ℝ≥0∞) * (δ m / ε) < 1 := by
    exact (tendsto_failureBound_nat.add hmul).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) + 0 < 1))
  filter_upwards [hN, hpositive, eventually_ge_atTop (200 : ℕ), hbudget]
    with m hmN hmpositive hm hmbudget
  intro R q₀ hq₀
  apply exists_realized_block_of_moment_budget hθ m j hm hj hmN r (samples m)
    hmpositive (δ := δ m) _ hmbudget hq₀ R
  intro k endpoint
  exact Finset.single_le_sum (s := Finset.univ) (a := (k, endpoint))
    (f := fun t : Fin r × Bool =>
      ∫⁻ phase, squaredError m (samples m t.1) t.2 phase ∂phaseLaw m (N m))
    (fun _ _ => zero_le) (Finset.mem_univ _)

end Invariant233.TrialSampling

end

end OAI
