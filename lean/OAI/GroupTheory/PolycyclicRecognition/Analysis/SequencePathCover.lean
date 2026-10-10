import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequencePathPacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LowerPacking

namespace OAI

/-! # Finite terminal covers from the controlled-height path estimate -/

noncomputable section
namespace PolycyclicRecognition

open Filter Metric Set
open scoped Topology Pointwise

theorem exists_sequence_path_cover
    {G W : Type*} [Group G] [MetricSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (π : G →* Multiplicative W) (E : Set W) (P : Set W → ℝ)
    (S : ℕ → Set G) (hS : ∀ n, TotallyBounded (S n))
    {K C b D : ℝ} (hC : 0 ≤ C) (hD : 0 < D) (k : ℕ)
    (hpaths : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ S n,
      ∃ γ : Path (1 : G) x,
        PathMetricBound γ (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
        ∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - scale n • z‖ ≤
          η * scale n + b * (1 + Real.log (2 + scale n)))
    (hupper : ∀ {r L κ B ε : ℝ}, 0 < r → 0 ≤ L → 0 ≤ κ → 0 ≤ ε →
      K * (κ + 2) + B ≤ r * ε → ∀ s : Finset G,
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ dist x y) →
      (∀ x ∈ s, ∃ γ : Path (1 : G) x, PathMetricBound γ L κ ∧
        ∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - r • z‖ ≤ B) →
      (s.card : ℝ) ≤ D * (3 + (L + 1) * (κ + 2)) ^ k *
        Real.exp (r * P (E + closedBall 0 ε))) :
    ∃ t : ℕ → Finset G, (∀ n, (↑(t n) : Set G) ⊆ S n) ∧
      (∀ n, ∀ x ∈ S n, ∃ y ∈ t n, dist x y ≤ 1) ∧
      ∀ ε : ℝ, 0 < ε → HasSubexponentialUpperBoundSeq scale
        (fun n => ((t n).card : ℝ) / Real.exp (scale n * P (E + closedBall 0 ε))) := by
  choose t ht hsep hcover using fun n =>
    exists_separated_net_of_totallyBounded (hS n) zero_lt_one
  refine ⟨t, ht, hcover, ?_⟩
  intro ε hε
  let H := 3 + (C + 1) * (3 * C + 2)
  have hH : 0 < H := by dsimp [H]; positivity
  have hpoly := (subexponential_upper_polynomial (mul_pos hD (pow_pos hH k)) (2 * k)).along_sequence hs
  have hbound : ∀ᶠ n in atTop,
      ((t n).card : ℝ) / Real.exp (scale n * P (E + closedBall 0 ε)) ≤
        (D * H ^ k) * (1 + scale n) ^ (2 * k) := by
    filter_upwards [hpaths (ε / 2) (half_pos hε), hs.eventually (eventually_ge_atTop (1 : ℝ)),
      hs.eventually (eventually_logarithmic_error_le (K * C + b) (2 * K) (half_pos hε))]
      with n hp hn herr
    have hr : 0 < scale n := by linarith
    have hlog : 0 ≤ 1 + Real.log (2 + scale n) := by
      have := Real.log_nonneg (show 1 ≤ 2 + scale n by linarith)
      linarith
    have he : K * (C * (1 + Real.log (2 + scale n)) + 2) +
        (ε / 2 * scale n + b * (1 + Real.log (2 + scale n))) ≤ scale n * ε := by
      nlinarith
    have hc := hupper hr (mul_nonneg hC hr.le) (mul_nonneg hC hlog) hε.le he (t n)
      (fun x hx y hy hxy => (hsep n x hx y hy hxy).le)
      (fun x hx => hp x (ht n hx))
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    apply hc.trans
    have hf := coarse_path_word_prefactor_le hC hn
    calc
      D * (3 + (C * scale n + 1) * (C * (1 + Real.log (2 + scale n)) + 2)) ^ k * _ ≤
          D * (H * (1 + scale n) ^ 2) ^ k * Real.exp (scale n * P (E + closedBall 0 ε)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ hD.le
        exact pow_le_pow_left₀ (by positivity) hf k
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  intro δ hδ
  filter_upwards [hbound, hpoly δ hδ] with n hb hp
  exact hb.trans hp

end PolycyclicRecognition

end

end OAI
