import OAI.Analysis.IrrationalRotation.Sampling.TrialSamplingActualMoments
import OAI.Analysis.IrrationalRotation.Sampling.CharacterSamplingStage

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Invariant233.TrialSampling

theorem eventually_actual_moment_budget (r : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ (m : ℕ) in atTop,
      ENNReal.ofReal (ProductPhases.failureBound m) +
        (2 * r : ℝ≥0∞) *
          (ENNReal.ofReal (SamplingAsymptotics.meanSquareBound 3509 m) /
            ENNReal.ofReal (ρ ^ 2)) < 1 := by
  have hε0 : ENNReal.ofReal (ρ ^ 2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hρ))
  have hδ := SamplingAsymptotics.tendsto_ofReal_meanSquareBound 3509 (by norm_num)
  have hdiv : Tendsto (fun m =>
      ENNReal.ofReal (SamplingAsymptotics.meanSquareBound 3509 m) /
        ENNReal.ofReal (ρ ^ 2)) atTop (𝓝 0) := by
    simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hδ (Or.inr hε0)
  have hmul : Tendsto (fun m => (2 * r : ℝ≥0∞) *
      (ENNReal.ofReal (SamplingAsymptotics.meanSquareBound 3509 m) /
        ENNReal.ofReal (ρ ^ 2))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul (a := (2 * r : ℝ≥0∞)) hdiv
        (Or.inr (by finiteness))
  exact (tendsto_failureBound_nat.add hmul).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) + 0 < 1))

theorem eventually_exists_prescribed_sampling_stage {θ : ℝ} (hθ : Irrational θ)
    (r : ℕ) (shift width : Fin r → ℝ) (hwidth : ∀ t, 0 < width t)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, 2 < N → N ≤ m ^ 2 →
      ∀ (R : ℝ) (q₀ : ℕ), 0 < q₀ →
      ∃ samples : Fin r → Finset ℕ,
        (∀ t : Fin r,
          (samples t).Nonempty ∧
          (∀ n ∈ samples t, ScalarSampling.samplingHorizon m / 2 ≤ (n : ℝ) ∧
            (n : ℝ) ≤ ScalarSampling.samplingHorizon m) ∧
          (∀ n ∈ samples t, Int.fract ((n : ℝ) * θ - shift t) ∈ Ioo 0 (width t)) ∧
          (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ ((samples t).card : ℝ) ∧
          (∀ n ∈ samples t, 0 < n) ∧
          ∀ n ∈ samples t, ∀ n' ∈ samples t, n ≠ n' →
            ScalarSampling.SamplingPair m N N n n') ∧
        ∃ q : ℕ → ℕ,
          q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
          (∀ i, q i ∣ q (i + 1)) ∧
          (∀ i < m, R ≤ (q (i + 1) : ℝ) / q i) ∧
          (∀ i : Fin m, Int.fract ((q (i.val + 1) : ℝ) * θ) ∈
            Ioo (1 / (N : ℝ)) (2 / (N : ℝ))) ∧
          ProductPhases.strictLargePhaseCondition Finset.univ (N : ℝ)
            (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)) ∧
          ∀ t endpoint,
            eLpNorm (fun x : Circle => average m (samples t) endpoint
              (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
              (fun i : Fin m => (q (i.val + 1) : ℤ) • x) - 1) 2 circleMeasure <
                ENNReal.ofReal ρ := by
  have hs := eventually_exists_scalar_ready_phase_samples hθ r shift width hwidth
  filter_upwards [hs, eventually_ge_atTop (200 : ℕ), eventually_actual_moment_budget r hρ]
    with m hms hm hbudget
  intro N hN hNm R q₀ hq₀
  have hNpos : 0 < N := by omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hNmreal : (N : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hNm
  obtain ⟨samples, hsample⟩ := hms N hNpos hNm
  refine ⟨samples, hsample, ?_⟩
  apply SamplingTests.exists_character_stage_of_moment_budget hθ hm
    (by exact_mod_cast hN) samples (fun t => (hsample t).2.2.2.2.1) hρ
    (δ := ENNReal.ofReal (SamplingAsymptotics.meanSquareBound 3509 m))
    ?_ (by simpa only [Fintype.card_fin] using hbudget) R hq₀
  intro t endpoint
  exact expectation_squaredError_le_actual_bound hm hNreal hNmreal (samples t)
    (hsample t).1 (hsample t).2.2.2.1 (fun n hn => ((hsample t).2.1 n hn).1)
    (hsample t).2.2.2.2.2 endpoint

end Invariant233.TrialSampling

end

end OAI
