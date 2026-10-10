import Mathlib
import OAI.Probability.ThreeState.Negative
import OAI.Probability.ThreeState.Supercritical

namespace OAI

/-! Threshold consequences on the proved parameter regions. -/

namespace ThreeState
open Filter Topology

lemma Nonreconstructs.not_reconstructs {a : ℕ → ℝ} (hz : Nonreconstructs a) :
    ¬ Reconstructs a := by
  rintro ⟨L, hL, hlim⟩
  have he : L = 0 := tendsto_nhds_unique hlim hz
  exact (ne_of_gt hL) he

 

theorem observed_nonreconstructs_iff_not_reconstructs (offspring : PMF ℕ)
    (lam : ℝ) (h : Admissible lam) :
    Nonreconstructs (fun n => advantage (observedLaw offspring lam h n)) ↔
      ¬ Reconstructs (fun n => advantage (observedLaw offspring lam h n)) := by
  refine ⟨Nonreconstructs.not_reconstructs, ?_⟩
  intro hn
  obtain ⟨L, hL, _, hlim⟩ := observedAdvantage_tendsto offspring lam h
  have he : L = 0 := by
    by_contra hne
    exact hn ⟨L, lt_of_le_of_ne hL (Ne.symm hne), hlim⟩
  simpa only [Nonreconstructs, he] using hlim

 

theorem regular_nonreconstruction_in_proved_region (b : ℕ) (hb : 2 ≤ b)
    (lam : ℝ) (h : Admissible lam) (hc : (b : ℝ) * lam ^ 2 ≤ 1)
    (hregion : 0 ≤ lam ∨ (b : ℝ) * |lam| ≤ 1 ∨ 4 * (b : ℝ) * lam ^ 2 ≤ 1) :
    Nonreconstructs (regularAdvantage b lam h) := by
  rcases hregion with hn | hD | hs
  · exact regular_nonnegative_nonreconstruction b hb lam h hn hc
  · exact regular_dobrushin_nonreconstruction b hb lam h hD
  · by_cases hn : 0 ≤ lam
    · exact regular_nonnegative_nonreconstruction b hb lam h hn hc
    · exact regular_small_negative_nonreconstruction b hb lam h (lt_of_not_ge hn).le hs

 

theorem poisson_nonreconstruction_in_proved_region (d : ℝ) (hd : 1 < d)
    (lam : ℝ) (h : Admissible lam) (hc : d * lam ^ 2 ≤ 1)
    (hregion : 0 ≤ lam ∨ d * |lam| ≤ 1 ∨ 4 * d * lam ^ 2 ≤ 1) :
    Nonreconstructs (poissonAdvantage d hd lam h) := by
  rcases hregion with hn | hD | hs
  · exact poisson_nonnegative_nonreconstruction d hd lam h hn hc
  · exact poisson_dobrushin_nonreconstruction d hd lam h hD
  · by_cases hn : 0 ≤ lam
    · exact poisson_nonnegative_nonreconstruction d hd lam h hn hc
    · exact poisson_small_negative_nonreconstruction d hd lam h (lt_of_not_ge hn).le hs

 

theorem regular_threshold_in_proved_region (b : ℕ) (hb : 2 ≤ b) (lam : ℝ)
    (h : Admissible lam)
    (hregion : 1 < (b : ℝ) * lam ^ 2 ∨ 0 ≤ lam ∨
      (b : ℝ) * |lam| ≤ 1 ∨ 4 * (b : ℝ) * lam ^ 2 ≤ 1) :
    (Reconstructs (regularAdvantage b lam h) ↔ 1 < (b : ℝ) * lam ^ 2) ∧
    ((b : ℝ) * lam ^ 2 ≤ 1 → Nonreconstructs (regularAdvantage b lam h)) := by
  have hz (hc : (b : ℝ) * lam ^ 2 ≤ 1) :
      Nonreconstructs (regularAdvantage b lam h) := by
    rcases hregion with hsuper | hknown
    · exact False.elim ((not_lt_of_ge hc) hsuper)
    · exact regular_nonreconstruction_in_proved_region b hb lam h hc hknown
  refine ⟨⟨?_, regular_supercritical b hb lam h⟩, hz⟩
  intro hr
  by_contra hcrit
  exact (hz (le_of_not_gt hcrit)).not_reconstructs hr

 

theorem poisson_threshold_in_proved_region (d : ℝ) (hd : 1 < d) (lam : ℝ)
    (h : Admissible lam)
    (hregion : 1 < d * lam ^ 2 ∨ 0 ≤ lam ∨ d * |lam| ≤ 1 ∨ 4 * d * lam ^ 2 ≤ 1) :
    (Reconstructs (poissonAdvantage d hd lam h) ↔ 1 < d * lam ^ 2) ∧
    (d * lam ^ 2 ≤ 1 → Nonreconstructs (poissonAdvantage d hd lam h)) := by
  have hz (hc : d * lam ^ 2 ≤ 1) : Nonreconstructs (poissonAdvantage d hd lam h) := by
    rcases hregion with hsuper | hknown
    · exact False.elim ((not_lt_of_ge hc) hsuper)
    · exact poisson_nonreconstruction_in_proved_region d hd lam h hc hknown
  refine ⟨⟨?_, poisson_supercritical d hd lam h⟩, hz⟩
  intro hr
  by_contra hcrit
  exact (hz (le_of_not_gt hcrit)).not_reconstructs hr

 

theorem regular_nonnegative_threshold (b : ℕ) (hb : 2 ≤ b) (lam : ℝ)
    (h : Admissible lam) (hn : 0 ≤ lam) :
    (Reconstructs (regularAdvantage b lam h) ↔ 1 < (b : ℝ) * lam ^ 2) ∧
    ((b : ℝ) * lam ^ 2 ≤ 1 → Nonreconstructs (regularAdvantage b lam h)) :=
  regular_threshold_in_proved_region b hb lam h (Or.inr (Or.inl hn))

 

theorem poisson_nonnegative_threshold (d : ℝ) (hd : 1 < d) (lam : ℝ)
    (h : Admissible lam) (hn : 0 ≤ lam) :
    (Reconstructs (poissonAdvantage d hd lam h) ↔ 1 < d * lam ^ 2) ∧
    (d * lam ^ 2 ≤ 1 → Nonreconstructs (poissonAdvantage d hd lam h)) :=
  poisson_threshold_in_proved_region d hd lam h (Or.inr (Or.inl hn))

 

theorem binary_exact_threshold (lam : ℝ) (h : Admissible lam) :
    (Reconstructs (regularAdvantage 2 lam h) ↔ 1 < (2 : ℝ) * lam ^ 2) ∧
    ((2 : ℝ) * lam ^ 2 ≤ 1 → Nonreconstructs (regularAdvantage 2 lam h)) := by
  apply regular_threshold_in_proved_region 2 (by omega) lam h
  by_cases hn : 0 ≤ lam
  · exact Or.inr (Or.inl hn)
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [abs_of_nonpos (lt_of_not_ge hn).le]
    norm_num
    linarith [h.1]

 

theorem poisson_le_two_exact_threshold (d : ℝ) (hd : 1 < d) (hupper : d ≤ 2)
    (lam : ℝ) (h : Admissible lam) :
    (Reconstructs (poissonAdvantage d hd lam h) ↔ 1 < d * lam ^ 2) ∧
    (d * lam ^ 2 ≤ 1 → Nonreconstructs (poissonAdvantage d hd lam h)) := by
  apply poisson_threshold_in_proved_region d hd lam h
  by_cases hn : 0 ≤ lam
  · exact Or.inr (Or.inl hn)
  · refine Or.inr (Or.inr (Or.inl ?_))
    have hs : |lam| ≤ 1 / 2 := by
      rw [abs_of_nonpos (lt_of_not_ge hn).le]
      linarith [h.1]
    nlinarith [mul_nonneg (show 0 ≤ d by linarith)
      (show 0 ≤ 1 / 2 - |lam| by linarith)]

end ThreeState

end OAI
