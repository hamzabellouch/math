import Mathlib

namespace OAI

/-! The diagonal quantifier step in the uniform ribbon passage proof.
Uniform probability, mass threshold and mesh cutoff follow once every
vanishing-mesh sequence admits one positive eventual lower bound. -/

noncomputable section
open Set Filter
open scoped Topology ENNReal

namespace SLEExactGauge

theorem uniform_passage_threshold_of_sequences
    {A : Type*} (p : A → ℝ → ℝ → ℝ≥0∞)
    (hmono : ∀ a v, Antitone (p a v))
    (hsequence : ∀ (a : ℕ → A) (v : ℕ → ℝ), (∀ n, 0 < v n) →
      Tendsto v atTop (𝓝 0) →
      ∃ c : ℝ, 0 < c ∧ ∃ q : ℝ≥0∞, 0 < q ∧
        ∀ᶠ n in atTop, q ≤ p (a n) (v n) c) :
    ∃ q c v₀ : ℝ, 0 < q ∧ 0 < c ∧ 0 < v₀ ∧
      ∀ a : A, ∀ v : ℝ, 0 < v → v < v₀ → ENNReal.ofReal q ≤ p a v c := by
  classical
  by_contra h
  push Not at h
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hfail (n : ℕ) : ∃ a : A, ∃ v : ℝ,
      0 < v ∧ v < ε n ∧ p a v (ε n) < ENNReal.ofReal (ε n) := by
    obtain ⟨a, v, hv, hvs, hp⟩ := h (ε n) (ε n) (ε n) (hε n) (hε n) (hε n)
    exact ⟨a, v, hv, hvs, hp⟩
  choose a v hv hvs hbad using hfail
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hvlim : Tendsto v atTop (𝓝 0) :=
    squeeze_zero (fun n => (hv n).le) (fun n => (hvs n).le) hεlim
  obtain ⟨c, hc, q, hq, hlower⟩ := hsequence a v hv hvlim
  have hsmall : ∀ᶠ n in atTop, ε n ≤ c :=
    (hεlim.eventually (gt_mem_nhds hc)).mono fun _ h => h.le
  have hupper : ∀ᶠ n in atTop, q ≤ ENNReal.ofReal (ε n) := by
    filter_upwards [hlower, hsmall] with n hn hs
    exact (hn.trans (hmono (a n) (v n) hs)).trans (hbad n).le
  have hlim : Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hεlim
  exact (not_le_of_gt hq) (ge_of_tendsto hlim hupper)

end SLEExactGauge

end

end OAI
