import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.DyadicApproximateFits
import OAI.Analysis.RieszRectifiability.Foundations.DyadicDistanceSteps
import OAI.Analysis.RieszRectifiability.Foundations.DyadicDistanceSum
import OAI.Analysis.RieszRectifiability.Flatness.PlaneMomentTransfer

namespace OAI

/-!
# Dyadic moments relative to one fixed plane

Approximate excess minimizers provide an affine plane at each dyadic radius.
Summing the adjacent distance-transfer estimates controls the squared distance to
the initial plane on every larger ball, uniformly in the measure and number of scales.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_fixed_plane_dyadic_moments {n d : ℕ} (hnd : n ≤ d)
    (C c b : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hb : 1 < b) :
    ∃ M κ : ℝ, 0 < M ∧ 0 < κ ∧
      ∀ μ : Measure (Ambient d), IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth n C μ →
      ∀ N : ℕ, ∀ δ : ℝ, 0 < δ → δ * b ^ N ≤ κ →
      (∀ i ≤ N, c * ((2 : ℝ) ^ i) ^ n ≤ μ.real (ball (0 : Ambient d) ((2 : ℝ) ^ i))) →
      (∀ i ≤ N, squaredExcess n μ 0 ((2 : ℝ) ^ i) ≤ (δ * b ^ i) ^ 2) →
      ∃ P : ℕ → AffineSubspace ℝ (Ambient d), (∀ i, IsAffineNPlane n (P i)) ∧
        (∀ i ≤ N, (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i),
          infDist x (P i : Set (Ambient d)) ^ 2 ∂μ) ≤
            2 * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2)) ∧
        ∀ l ≤ N, (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l),
          infDist x (P 0 : Set (Ambient d)) ^ 2 ∂μ) ≤
            M * (δ * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2) := by
  obtain ⟨B, κ, hB, hκ, hsteps⟩ := exists_uniform_dyadic_distance_steps n d C c b hC hc hb
  let K := B * (3 / (2 * b - 1) + 1 / (b - 1))
  have hden1 : 0 < b - 1 := sub_pos.mpr hb
  have hden2 : 0 < 2 * b - 1 := by linarith
  have hK : 0 < K := by dsimp only [K]; positivity
  let M := 4 + 2 * C * K ^ 2
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨M, κ, hM, hκ, ?_⟩
  intro μ hfinite hg N δ hδ hsmall hmass hexcess
  let : IsFiniteMeasureOnCompacts μ := hfinite
  obtain ⟨P, hP, hfit⟩ := exists_dyadic_approximate_fits hnd μ δ b hδ (by linarith) N hexcess
  have hstep := hsteps μ hfinite hg N δ hδ hsmall P hP hmass hfit
  refine ⟨P, hP, hfit, ?_⟩
  intro l hl
  have hpoint : ∀ x ∈ ball (0 : Ambient d) ((2 : ℝ) ^ l),
      infDist x (P 0 : Set (Ambient d)) ≤ infDist x (P l : Set (Ambient d)) +
        K * (δ * b ^ l) * (2 : ℝ) ^ l := by
    intro x hx
    have hxnorm : ‖x‖ ≤ (2 : ℝ) ^ l := by
      have hlt : ‖x‖ < (2 : ℝ) ^ l := by simpa only [mem_ball, dist_zero_right] using! hx
      exact hlt.le
    have h := dyadic_distance_chain_bound (fun i => infDist x (P i : Set (Ambient d)))
      B δ b ‖x‖ hB.le hδ.le hb (norm_nonneg x) l hxnorm
      (fun i hi => hstep i (lt_of_lt_of_le hi hl) x)
    convert! h using 1
    dsimp only [K]
    ring
  have h := plane_second_moment_bound_from_distance_transfer μ C hg (P 0) (P l)
    (hP 0).1 (hP l).1 ((2 : ℝ) ^ l) (δ * b ^ l) K 2 (by positivity)
    (by positivity) hK.le (hfit l hl) hpoint
  simpa only [M, show (2 : ℝ) * 2 = 4 by norm_num] using! h

end

end RieszRectifiability

end OAI
