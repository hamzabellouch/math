import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.OpenPlaneBoxes
import OAI.Analysis.RieszRectifiability.Kernel.LocalizedRieszPairingBounds

namespace OAI

/-!
# Compactly supported pairing tails

Global upper growth bounds the integral of a bounded, compactly supported test
function. This gives an explicit constant for the inverse-radius error between
the scalar Riesz pairing and its interior product-measure integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem compact_supported_abs_integral_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (H : ℝ) (hH : 0 ≤ H)
    (φ : Ambient d → ℝ) (hφ : Continuous φ) (B : ℝ≥0)
    (hB : ∀ x, |φ x| ≤ (B : ℝ)) (hs : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    Integrable φ μ ∧ (∫ x, |φ x| ∂μ) ≤ (B : ℝ) * (C * (H + 1) ^ m) := by
  let := hg.finite_on_compacts
  have hcomp : HasCompactSupport φ := by
    apply HasCompactSupport.intro (isCompact_closedBall a H)
    intro x hx
    by_contra hn
    exact hx (hs x hn)
  have hi := hφ.integrable_of_hasCompactSupport (μ := μ) hcomp
  have hzero : ∀ x ∉ ball a (H + 1), |φ x| = 0 := by
    intro x hx
    have hz : φ x = 0 := by
      by_contra hn
      exact hx ((hs x hn).trans_lt (by linarith : H < H + 1))
    rw [hz, abs_zero]
  have hR : 0 < H + 1 := by positivity
  have hfinite : μ (ball a (H + 1)) < ∞ := (hg.2 a _ hR).trans_lt ENNReal.ofReal_lt_top
  have hmass : μ.real (ball a (H + 1)) ≤ C * (H + 1) ^ m :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg hR.le _)) (hg.2 a _ hR)
  refine ⟨hi, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    _ = ‖∫ x in ball a (H + 1), |φ x| ∂μ‖ :=
      (Real.norm_of_nonneg (integral_nonneg fun x => abs_nonneg _)).symm
    _ ≤ (B : ℝ) * μ.real (ball a (H + 1)) :=
      norm_setIntegral_le_of_norm_le_const hfinite fun x _ => by
        simpa only [Real.norm_eq_abs, abs_abs] using! hB x
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass B.coe_nonneg

def compactRieszTailConstant (m : ℕ) (C : ℝ) {d : ℕ} (e : Ambient d) (H : ℝ) (B : ℝ≥0) : ℝ :=
  (2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) *
    (‖e‖ * H * ((B : ℝ) * (C * (H + 1) ^ m))) * (2 * (C * 2 ^ m))

theorem compactRieszTailConstant_nonneg (m : ℕ) (C : ℝ) {d : ℕ} (e : Ambient d)
    (H : ℝ) (B : ℝ≥0) (hC : 0 ≤ C) (hH : 0 ≤ H) :
    0 ≤ compactRieszTailConstant m C e H B := by
  unfold compactRieszTailConstant
  positivity

theorem rieszScalarPairing_interior_tail_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (e : Ambient d) (φ : Ambient d → ℝ) (L B : ℝ≥0)
    (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (hs : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    |rieszScalarPairing m μ a R e φ - (1 / 2 : ℝ) *
      (∫ q, rieszInteriorIntegrand m e φ q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R)))| ≤
      compactRieszTailConstant m C e H B / R := by
  have hC : 0 ≤ C := hg.1
  obtain ⟨hi, hmass⟩ := compact_supported_abs_integral_bound m C μ hg a H hH φ hφ.continuous B hB hs
  have hlocal : (∫ x in ball a R, |φ x| ∂μ) ≤ (B : ℝ) * (C * (H + 1) ^ m) :=
    (setIntegral_le_integral hi.abs (Eventually.of_forall fun x => abs_nonneg (φ x))).trans hmass
  have hb := rieszFarIntegrand_integral_abs_bound m C μ hg e φ L hφ a H R hH hR hHR hs
  have hf := abs_integral_le_integral_abs.trans hb
  unfold rieszScalarPairing
  dsimp only
  rw [add_sub_cancel_left]
  calc
    _ ≤ _ := hf
    _ ≤ (2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) *
        (‖e‖ * H * ((B : ℝ) * (C * (H + 1) ^ m))) * (2 * (C * 2 ^ m / R)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = _ := by unfold compactRieszTailConstant; ring

end

end RieszRectifiability

end OAI
