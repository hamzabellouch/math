import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NormalizedTailDecay

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem dyadic_shifted_last_error_identity (q N : ℕ) (hN : q + 1 ≤ N) (δ : ℝ) :
    ((2 : ℝ) ^ q * 2 ^ (N - (q + 1)))⁻¹ / δ = 2 * (((2 : ℝ) ^ N)⁻¹ / δ) := by
  have hp : (2 : ℝ) ^ (q + 1) * 2 ^ (N - (q + 1)) = (2 : ℝ) ^ N := by
    rw [← pow_add, Nat.add_sub_of_le hN]
  rw [pow_succ] at hp
  have hr : (2 : ℝ) ^ q * 2 ^ (N - (q + 1)) = (2 : ℝ) ^ N / 2 := by nlinarith [hp]
  rw [hr, inv_div]
  ring

theorem dyadic_shifted_last_error_tendsto (q : ℕ) (N : ℕ → ℕ) (δ : ℕ → ℝ)
    (hN : Tendsto N atTop atTop)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0)) :
    Tendsto (fun j => N j - (q + 1)) atTop atTop ∧
      Tendsto (fun j => ((2 : ℝ) ^ q * 2 ^ (N j - (q + 1)))⁻¹ / δ j) atTop (𝓝 0) := by
  refine ⟨(tendsto_sub_atTop_nat (q + 1)).comp hN, ?_⟩
  have h := hlast.const_mul 2
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [hN.eventually (eventually_ge_atTop (q + 1))] with j hj
  exact (dyadic_shifted_last_error_identity q (N j) hj (δ j)).symm

theorem dyadic_ball_to_shell_moment_identity (m q k : ℕ) (D δ b : ℝ) :
    δ ^ 2 * D * ((2 : ℝ) ^ (q + k + 1)) ^ m *
        ((2 : ℝ) ^ (q + k + 1) * b ^ (q + k + 1)) ^ 2 =
      ((D * (2 : ℝ) ^ (m + 2) * (b ^ (q + 1)) ^ 2) * ((2 : ℝ) ^ q * 2 ^ k) ^ m) *
        (δ * ((2 : ℝ) ^ q * 2 ^ k) * b ^ k) ^ 2 := by
  simp only [pow_add, pow_succ, mul_pow]
  ring

theorem controlled_shell_moments_from_dyadic_balls {d : ℕ} (m : ℕ)
    (μ : ℕ → Measure (Ambient d)) (a : Ambient d) (u : ℕ → Ambient d → ℝ)
    (δ : ℕ → ℝ) (N : ℕ → ℕ) (D b Bmin : ℝ)
    (hw : ∀ l j, MemLp (u j) 2 ((μ j).restrict (ball a ((2 : ℝ) ^ l))))
    (hbound : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ m * ((2 : ℝ) ^ l * b ^ l) ^ 2) (q : ℕ) :
    ∃ B : ℝ, Bmin ≤ B ∧ ∀ j k, k < N j - (q + 1) →
      (∫ x in dyadicAnnulus a ((2 : ℝ) ^ q) k, u j x ^ 2 ∂μ j) ≤
        (B * ((2 : ℝ) ^ q * 2 ^ k) ^ m) * (δ j * ((2 : ℝ) ^ q * 2 ^ k) * b ^ k) ^ 2 := by
  let B₀ := D * (2 : ℝ) ^ (m + 2) * (b ^ (q + 1)) ^ 2
  refine ⟨max Bmin B₀, le_max_left _ _, ?_⟩
  intro j k hk
  have hcontrol : q + k + 1 ≤ N j := by omega
  have hsub : dyadicAnnulus a ((2 : ℝ) ^ q) k ⊆ ball a ((2 : ℝ) ^ (q + k + 1)) := by
    convert! dyadicAnnulus_subset_ball a ((2 : ℝ) ^ q) k using 1
    rw [← pow_add]
    congr 2
  calc
    _ ≤ ∫ x in ball a ((2 : ℝ) ^ (q + k + 1)), u j x ^ 2 ∂μ j :=
      integral_mono_measure (Measure.restrict_mono hsub le_rfl)
        (Eventually.of_forall (fun x => sq_nonneg (u j x))) (hw (q + k + 1) j).integrable_sq
    _ ≤ δ j ^ 2 * D * ((2 : ℝ) ^ (q + k + 1)) ^ m *
        ((2 : ℝ) ^ (q + k + 1) * b ^ (q + k + 1)) ^ 2 := hbound j (q + k + 1) hcontrol
    _ = (B₀ * ((2 : ℝ) ^ q * 2 ^ k) ^ m) *
        (δ j * ((2 : ℝ) ^ q * 2 ^ k) * b ^ k) ^ 2 :=
      dyadic_ball_to_shell_moment_identity m q k D (δ j) b
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right Bmin B₀) (by positivity)) (sq_nonneg _)

end

end RieszRectifiability

end OAI
