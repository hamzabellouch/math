import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLipschitzAmplitude
import OAI.Analysis.RieszRectifiability.Kernel.OuterCutoffError

namespace OAI

/-!
# Outer-cutoff errors for mean-zero Lipschitz tests

Restricting the measure to a large ball changes a scalar Riesz pairing by a
controlled tail. The explicit oscillation constant combines the compact test's
amplitude bound with growth and cancellation estimates outside that ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def oscillationTailConstant (n : ℕ) (G J : ℝ) : ℝ :=
  (2 ^ (n + 1) + (n + 1 : ℝ) * 2 ^ (n + 2)) *
    (2 * J * (G * J ^ n)) * J * (2 * (G * 2 ^ n))

theorem oscillationTailConstant_nonneg (n : ℕ) (G J : ℝ) (hG : 0 ≤ G) (hJ : 0 ≤ J) :
    0 ≤ oscillationTailConstant n G J := by
  unfold oscillationTailConstant
  positivity

theorem original_test_outer_cutoff_error {d : ℕ} [Nontrivial (Ambient d)]
    (p : ℕ) (G : ℝ) (μ : Measure (Ambient d)) [SFinite μ]
    (hg : GlobalUpperGrowth (p + 1) G μ)
    (e : Ambient d) (he : ‖e‖ ≤ 1) (φ : Ambient d → ℝ) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (z a : Ambient d) (r J R T : ℝ)
    (hr : 0 < r) (hJ : 0 < J) (hR : 0 < R) (hsmall : 2 * (J * r) ≤ R)
    (hcontain : ball z R ⊆ ball a T)
    (hL : (L : ℝ) ≤ 1 / r) (hsupport : tsupport φ ⊆ ball z (J * r))
    (hzero : (∫ x, φ x ∂μ) = 0) :
    |rieszScalarPairing (p + 1) μ z (2 * (J * r)) e φ -
      rieszScalarPairing (p + 1) (μ.restrict (ball a T)) z (2 * (J * r)) e φ| ≤
      oscillationTailConstant (p + 1) G J * (r / R) * r ^ (p + 1) := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have hJr : 0 < J * r := mul_pos hJ hr
  have hs : ∀ x, φ x ≠ 0 → dist x z ≤ J * r :=
    fun x hx => (hsupport (subset_tsupport φ hx)).le
  have houter : ∀ x ∉ ball a T, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx (hcontain ((ball_subset_ball (by linarith)) (hsupport (subset_tsupport φ hn))))
  have hzeroν : (∫ x, φ x ∂μ.restrict (ball a T)) = 0 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero houter).trans hzero
  have heqμ := rieszScalarPairing_localization_independent p G μ hg e φ L hφ z z
    (J * r) (J * r) (2 * (J * r)) R hJr.le hJr.le (by positivity) hR le_rfl hsmall hs hs hzero
  have heqν := rieszScalarPairing_localization_independent p G (μ.restrict (ball a T))
    (globalGrowth_restrict (p + 1) G μ hg (ball a T)) e φ L hφ z z
    (J * r) (J * r) (2 * (J * r)) R hJr.le hJr.le (by positivity) hR le_rfl hsmall hs hs hzeroν
  rw [heqμ, heqν]
  have hI := (compact_lipschitz_test_memLp μ φ L hφ z (J * r) hsupport).2
  have hval := original_oscillation_test_amplitude φ L hφ z r J hr hJ hL hsupport
  have hmass : μ.real (ball z (J * r)) ≤ G * (J * r) ^ (p + 1) :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg hJr.le _)) (hg.2 z _ hJr)
  have hL1 : (∫ x in ball z R, |φ x| ∂μ) ≤ (2 * J) * (G * (J * r) ^ (p + 1)) := by
    calc
      _ ≤ ∫ x, |φ x| ∂μ := integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun x => abs_nonneg _) hI.abs
      _ ≤ (2 * J) * μ.real (ball z (J * r)) :=
        integral_abs_le_support_ball_mass μ φ hI z (J * r) (2 * J) hval
          (fun x hx => hsupport (subset_tsupport φ hx))
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  calc
    _ ≤ _ := riesz_pairing_outer_cutoff_error_bound (p + 1) G μ hg e φ L hφ z a
      (J * r) R T hJr.le hR hsmall hcontain hs
    _ ≤ (2 ^ (p + 1 + 1) + (p + 1 + 1 : ℝ) * 2 ^ (p + 1 + 2)) *
        (1 * (J * r) * ((2 * J) * (G * (J * r) ^ (p + 1)))) * (2 * (G * 2 ^ (p + 1) / R)) := by
      have hG := hg.1
      simp only [Nat.cast_add, Nat.cast_one]
      gcongr
    _ = _ := by
      unfold oscillationTailConstant
      simp only [Nat.cast_add, Nat.cast_one]
      rw [mul_pow]
      ring

end

end RieszRectifiability

end OAI
