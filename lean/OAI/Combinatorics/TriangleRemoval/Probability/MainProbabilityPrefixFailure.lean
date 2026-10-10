import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.EvolveBindFinish

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

theorem main_probability_prefix_failure_bound (c C : ℝ) (hc : 0 < c)
    (ε : ℝ) (hε : 0 < ε) : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      probability n (fun H => ε < |normalizedLeave n H-sharpConstant|) ≤
        (δ+(2*(n : ℝ)+1)*prefixFailure n c C)/ε^2 := by
  classical
  intro δ hδ
  filter_upwards [main_l2_prefix_failure_bound c C hc δ hδ] with n hn
  have hh := pmfMean_markov_sq (terminalLaw n)
    (fun H => normalizedLeave n H-sharpConstant) ε hε
  exact hh.trans (div_le_div_of_nonneg_right hn (sq_nonneg ε))

theorem main_expectation_prefix_failure_bound (c C : ℝ) (hc : 0 < c) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      (expectation n (normalizedLeave n)-sharpConstant)^2 ≤
        δ+(2*(n : ℝ)+1)*prefixFailure n c C := by
  intro δ hδ
  filter_upwards [main_l2_prefix_failure_bound c C hc δ hδ] with n hn
  have hh := pmfMean_sq_le (terminalLaw n) (fun H => normalizedLeave n H-sharpConstant)
  rw [pmfMean_sub,pmfMean_const] at hh
  exact hh.trans hn

lemma expectation_normalizedLeave (n : ℕ) :
    expectation n (normalizedLeave n) =
      expectation n (fun H => (H.card : ℝ))/normalization n := by
  change pmfMean (terminalLaw n) (fun graph => (graph.card : ℝ)/normalization n) =
    pmfMean (terminalLaw n) (fun graph => (graph.card : ℝ))/normalization n
  simp only [div_eq_mul_inv,pmfMean_mul_const]

end SharpTerminalLeave

end

end OAI
