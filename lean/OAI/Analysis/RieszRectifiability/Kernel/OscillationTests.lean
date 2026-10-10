import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.PairingLocalizationIndependence
import OAI.Analysis.RieszRectifiability.Kernel.LocalizedNormalTest

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

def ScalarOscillationBound {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (A v : ℝ) : Prop :=
  ∀ (e : Ambient d), ‖e‖ ≤ 1 → ∀ φ : Ambient d → ℝ,
    LipschitzWith 1 φ → tsupport φ ⊆ ball a A → (∫ x, φ x ∂μ) = 0 →
      |rieszScalarPairing m μ a (2 * A) e φ| ≤ v

theorem rieszInteriorIntegrand_const_mul {d : ℕ} (m : ℕ) (e : Ambient d)
    (φ : Ambient d → ℝ) (c : ℝ) (q : Ambient d × Ambient d) :
    rieszInteriorIntegrand m e (fun x => c * φ x) q = c * rieszInteriorIntegrand m e φ q := by
  unfold rieszInteriorIntegrand
  ring

theorem rieszFarIntegrand_const_mul {d : ℕ} (m : ℕ) (e : Ambient d)
    (φ : Ambient d → ℝ) (a : Ambient d) (c : ℝ) (q : Ambient d × Ambient d) :
    rieszFarIntegrand m e (fun x => c * φ x) a q = c * rieszFarIntegrand m e φ a q := by
  unfold rieszFarIntegrand
  ring

theorem rieszScalarPairing_const_mul {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (R : ℝ) (e : Ambient d) (φ : Ambient d → ℝ) (c : ℝ) :
    rieszScalarPairing m μ a R e (fun x => c * φ x) = c * rieszScalarPairing m μ a R e φ := by
  unfold rieszScalarPairing
  dsimp only
  simp_rw [rieszInteriorIntegrand_const_mul, rieszFarIntegrand_const_mul]
  rw [integral_const_mul, integral_const_mul]
  ring

theorem tsupport_subset_ball_of_support_bound {d : ℕ}
    (φ : Ambient d → ℝ) (a : Ambient d) (H A : ℝ) (hHA : H < A)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) : tsupport φ ⊆ ball a A := by
  have hclosed : tsupport φ ⊆ closedBall a H := by
    change closure (Function.support φ) ⊆ closedBall a H
    exact isClosed_closedBall.closure_subset_iff.mpr (fun x hx => hsupport x hx)
  intro x hx
  exact (hclosed hx).trans_lt hHA

theorem ScalarOscillationBound.lipschitz_test_bound {d : ℕ}
    (m : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) (A v : ℝ)
    (hosc : ScalarOscillationBound m μ a A v) (e : Ambient d) (he : ‖e‖ ≤ 1)
    (φ : Ambient d → ℝ) (D : ℝ≥0) (hφ : LipschitzWith D φ)
    (hsupport : tsupport φ ⊆ ball a A) (hzero : (∫ x, φ x ∂μ) = 0) :
    |rieszScalarPairing m μ a (2 * A) e φ| ≤ ((D : ℝ) + 1) * v := by
  let c : ℝ := (D : ℝ) + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hscaled := lipschitz_const_mul_real hφ c⁻¹
  have hcoef : ‖c⁻¹‖₊ * D ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
    rw [abs_of_pos (inv_pos.mpr hc)]
    have hDc : (D : ℝ) ≤ c := by dsimp [c]; linarith
    calc
      c⁻¹ * (D : ℝ) = (D : ℝ) / c := by ring
      _ ≤ 1 := (div_le_one hc).mpr hDc
  have hzero' : (∫ x, c⁻¹ * φ x ∂μ) = 0 := by rw [integral_const_mul, hzero, mul_zero]
  have hb := hosc e he (fun x => c⁻¹ * φ x) (hscaled.weaken hcoef)
    (tsupport_mul_subset_right.trans hsupport) hzero'
  rw [rieszScalarPairing_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hc)] at hb
  calc
    |rieszScalarPairing m μ a (2 * A) e φ| = c * (c⁻¹ * |rieszScalarPairing m μ a (2 * A) e φ|) := by
      field_simp
    _ ≤ c * v := mul_le_mul_of_nonneg_left hb hc.le

theorem oscillation_bound_for_localized_test {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (a : Ambient d) (A v : ℝ) (hA : 0 < A) (hosc : ScalarOscillationBound (p + 1) μ a A v)
    (e : Ambient d) (he : ‖e‖ ≤ 1) (φ : Ambient d → ℝ) (D : ℝ≥0) (hφ : LipschitzWith D φ)
    (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R) (hHA : H < A)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) (hzero : (∫ x, φ x ∂μ) = 0) :
    |rieszScalarPairing (p + 1) μ a R e φ| ≤ ((D : ℝ) + 1) * v := by
  have hsupport' : ∀ x, φ x ≠ 0 → dist x a ≤ A := fun x hx => (hsupport x hx).trans hHA.le
  have heq := rieszScalarPairing_localization_independent p C μ hg e φ D hφ a a H A R (2 * A)
    hH hA.le hR (by positivity) hHR le_rfl hsupport hsupport' hzero
  rw [heq]
  exact hosc.lipschitz_test_bound (p + 1) μ a A v e he φ D hφ
    (tsupport_subset_ball_of_support_bound φ a H A hHA hsupport) hzero

end

end RieszRectifiability

end OAI
