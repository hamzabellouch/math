import Mathlib
import OAI.Combinatorics.TriangleRemoval.Probability.PmfMeanAffineSq

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma evolve_bind_finish {n : ℕ} (G : Graph n) (k : ℕ) :
    (evolve G k).bind finish = finish G := by
  induction k with
  | zero => simp only [evolve,PMF.pure_bind]
  | succ k ih =>
    rw [evolve,PMF.bind_bind]
    have hh : (fun H : Graph n => (step H).bind finish) = finish := by
      funext H
      exact (finish_harmonic H).symm
    rw [hh,ih]

lemma terminalLaw_prefix_disintegration (n : ℕ) :
    terminalLaw n = (prefixLaw n).bind finish := by
  rw [prefixLaw,evolve_bind_finish]
  apply evolve_eq_finish
  simp only [completeGraph,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin,le_refl]

lemma normalizedLeave_error_envelope {n : ℕ} (hn : 0 < n) {H : Graph n}
    (hH : H ⊆ completeGraph n) :
    (normalizedLeave n H-sharpConstant)^2 ≤ 2*(n : ℝ)+1 := by
  have hcard : (H.card : ℝ) ≤ (n : ℝ)^2 := by
    have hh := (Finset.card_le_card hH).trans
      (show (completeGraph n).card ≤ n^2 by
        simpa only [completeGraph,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
          using Nat.choose_le_pow n 2)
    exact_mod_cast hh
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnorm := normalization_pos hn
  have hsq : (normalizedLeave n H)^2 ≤ (n : ℝ) := by
    unfold normalizedLeave
    rw [div_pow,normalization_sq]
    calc
      _ ≤ ((n : ℝ)^2)^2/(n : ℝ)^3 := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg H.card) hcard 2) (by positivity)
      _ = _ := by field_simp
  have ha := sharpConstant_sq
  nlinarith [sq_nonneg (normalizedLeave n H+sharpConstant)]

theorem main_l2_prefix_failure_bound (c C : ℝ) (hc : 0 < c) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      expectation n (fun H => (normalizedLeave n H-sharpConstant)^2) ≤
        δ+(2*(n : ℝ)+1)*prefixFailure n c C := by
  classical
  intro δ hδ
  filter_upwards [goodPrefix_normalized_l2 c C hc δ hδ,eventually_ge_atTop (1 : ℕ)] with n hg hn
  have hn0 : 0 < n := by omega
  change pmfMean (terminalLaw n) (fun H => (normalizedLeave n H-sharpConstant)^2) ≤ _
  rw [terminalLaw_prefix_disintegration,pmfMean_bind]
  calc
    _ ≤ pmfMean (prefixLaw n) (fun G => δ+(2*(n : ℝ)+1)*
          (if GoodPrefixGraph n c C G then 0 else 1)) := by
      apply pmfMean_mono
      intro G hG
      by_cases hgood : GoodPrefixGraph n c C G
      · simp only [ite_eq_left hgood,mul_zero,add_zero]
        exact (hg G hgood).le
      · simp only [ite_eq_right hgood,mul_one]
        have hsub : G ⊆ completeGraph n := evolve_support_subset _ _ hG
        have hh : pmfMean (finish G) (fun H => (normalizedLeave n H-sharpConstant)^2) ≤
            2*(n : ℝ)+1 := by
          rw [← pmfMean_const (finish G) (2*(n : ℝ)+1)]
          apply pmfMean_mono
          intro H hH
          exact normalizedLeave_error_envelope hn0 ((finish_support_subset hH).trans hsub)
        linarith
    _ = _ := by rw [pmfMean_add,pmfMean_const,pmfMean_const_mul]; rfl

end SharpTerminalLeave

end

end OAI
