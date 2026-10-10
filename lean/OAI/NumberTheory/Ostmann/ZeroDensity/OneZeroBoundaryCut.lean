import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace OAI

/-! # Choosing one of two left boundaries away from a unique real zero -/

namespace Ostmann

open Complex

theorem exists_two_point_cut (δ β : ℝ) (hδ : 0 < δ) :
    ∃ a : ℝ, 1 - 2 * δ ≤ a ∧ a ≤ 1 - δ ∧ δ / 2 ≤ |a - β| := by
  by_cases hβ : β ≤ 1 - 3 * δ / 2
  · refine ⟨1 - δ, by linarith, le_rfl, ?_⟩
    exact (show δ / 2 ≤ 1 - δ - β by linarith).trans (le_abs_self _)
  · refine ⟨1 - 2 * δ, le_rfl, by linarith, ?_⟩
    exact (show δ / 2 ≤ -(1 - 2 * δ - β) by linarith).trans (neg_le_abs _)

theorem one_zero_boundary_cut (Z : ℕ → ℂ) (δ T : ℝ)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (hT : 2 ≤ T)
    (hreal : ∀ i, |(Z i).im| ≤ T + 2 → 1 - 4 * δ ≤ (Z i).re → (Z i).im = 0)
    (hunique : ∀ i j, |(Z i).im| ≤ T + 2 → |(Z j).im| ≤ T + 2 →
      1 - 4 * δ ≤ (Z i).re → 1 - 4 * δ ≤ (Z j).re → i = j) :
    ∃ a : ℝ, 1 - 2 * δ ≤ a ∧ a ≤ 1 - δ ∧
      ∀ s : ℂ, ((s.re = a ∧ |s.im| ≤ T) ∨ (a ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| = T)) →
      ∀ i : ℕ, δ / 2 ≤ ‖s - Z i‖ := by
  classical
  have hcut : ∃ a : ℝ, 1 - 2 * δ ≤ a ∧ a ≤ 1 - δ ∧
      ∀ i, |(Z i).im| ≤ T + 2 → 1 - 4 * δ ≤ (Z i).re → δ / 2 ≤ |a - (Z i).re| := by
    by_cases hex : ∃ i, |(Z i).im| ≤ T + 2 ∧ 1 - 4 * δ ≤ (Z i).re
    · obtain ⟨i, hi, hni⟩ := hex
      obtain ⟨a, ha, ha', hagap⟩ := exists_two_point_cut δ (Z i).re hδ
      refine ⟨a, ha, ha', ?_⟩
      intro j hj hnj
      have he := hunique j i hj hi hnj hni
      simpa only [he] using hagap
    · refine ⟨1 - δ, by linarith, le_rfl, ?_⟩
      intro i hi hni
      exact (hex ⟨i, hi, hni⟩).elim
  obtain ⟨a, ha, ha', hasep⟩ := hcut
  refine ⟨a, ha, ha', ?_⟩
  intro s hs i
  have hsa : a ≤ s.re := by rcases hs with h | h <;> linarith [h.1]
  have hst : |s.im| ≤ T := by
    rcases hs with h | h
    · exact h.2
    · exact h.2.2.le
  by_cases hi : |(Z i).im| ≤ T + 2
  · by_cases hni : 1 - 4 * δ ≤ (Z i).re
    · rcases hs with hs | hs
      · have hg := hasep i hi hni
        have hn := Complex.abs_re_le_norm (s - Z i)
        simp only [Complex.sub_re, hs.1] at hn
        exact hg.trans hn
      · have him := hreal i hi hni
        have hn := Complex.abs_im_le_norm (s - Z i)
        rw [Complex.sub_im, him, sub_zero, hs.2.2] at hn
        linarith
    · have hn := Complex.re_le_norm (s - Z i)
      simp only [Complex.sub_re] at hn
      linarith
  · have htall := abs_add_le (s.im - (Z i).im) (-s.im)
    rw [show s.im - (Z i).im + -s.im = -(Z i).im by ring, abs_neg, abs_neg] at htall
    have hn := Complex.abs_im_le_norm (s - Z i)
    simp only [Complex.sub_im] at hn
    linarith [lt_of_not_ge hi]

end Ostmann

end OAI
