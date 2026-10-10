import OAI.Analysis.IrrationalRotation.Model.ScalarSamplingEstimates
import OAI.Analysis.IrrationalRotation.Sampling.SyndeticSampling

namespace OAI

namespace Invariant233.TrialSampling
open Filter

theorem samplingPair_of_nat_separation {m N n n' : ℕ}
    (hN : 0 < N) (hNm : N ≤ m ^ 2) (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hrange : ScalarSampling.samplingHorizon m / 2 ≤ (n : ℝ) ∧
      (n : ℝ) ≤ ScalarSampling.samplingHorizon m)
    (hrange' : ScalarSampling.samplingHorizon m / 2 ≤ (n' : ℝ) ∧
      (n' : ℝ) ≤ ScalarSampling.samplingHorizon m)
    (hsep : ∀ v v' : ℤ, |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
      (v ≠ 0 ∨ v' ≠ 0) →
        (N * m ^ 1000 : ℕ) < |v * (n : ℤ) + v' * (n' : ℤ)|) :
    ScalarSampling.SamplingPair m N N n n' where
  N₀_pos := by exact_mod_cast hN
  N₀_le := le_rfl
  N_le := by exact_mod_cast hNm
  n_pos := hn
  n'_pos := hn'
  distinct := hne
  first_range := hrange
  second_range := hrange'
  separated := by
    intro v v' hv hv' hvv
    exact_mod_cast hsep v v' hv hv' hvv

theorem eventually_exists_scalar_ready_phase_samples {θ : ℝ} (hθ : Irrational θ)
    (q : ℕ) (shift width : Fin q → ℝ) (hwidth : ∀ r, 0 < width r) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, 0 < N → N ≤ m ^ 2 →
      ∃ samples : Fin q → Finset ℕ, ∀ r : Fin q,
        (samples r).Nonempty ∧
        (∀ n ∈ samples r, ScalarSampling.samplingHorizon m / 2 ≤ (n : ℝ) ∧
          (n : ℝ) ≤ ScalarSampling.samplingHorizon m) ∧
        (∀ n ∈ samples r, Int.fract ((n : ℝ) * θ - shift r) ∈ Set.Ioo 0 (width r)) ∧
        (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ ((samples r).card : ℝ) ∧
        (∀ n ∈ samples r, 0 < n) ∧
        ∀ n ∈ samples r, ∀ n' ∈ samples r, n ≠ n' →
          ScalarSampling.SamplingPair m N N n n' := by
  have hs := SyndeticSampling.eventually_exists_simultaneous_phase_sampling_powers
    hθ q shift width hwidth
  filter_upwards [hs, eventually_ge_atTop (1 : ℕ)] with m hm hm1
  intro N hN hNm
  obtain ⟨samples, hsample⟩ := hm N hNm
  refine ⟨samples, ?_⟩
  intro r
  obtain ⟨hrange, hphase, hcard, hpos, hsep⟩ := hsample r
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hc : 0 < ((samples r).card : ℝ) :=
    (Real.rpow_pos_of_pos hmpos _).trans_le hcard
  refine ⟨Finset.card_pos.mp (by exact_mod_cast hc), hrange, hphase, hcard, hpos, ?_⟩
  intro n hn n' hn' hne
  exact samplingPair_of_nat_separation hN hNm (hpos n hn) (hpos n' hn') hne
    (hrange n hn) (hrange n' hn') (hsep n hn n' hn' hne)

end Invariant233.TrialSampling

end OAI
