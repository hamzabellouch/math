import OAI.NumberTheory.JointDickman.Amplification.OscillatoryTests
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! # Scaling the smooth oscillatory test -/

namespace JointDickman

open MeasureTheory

noncomputable def scaledOscillatoryTest (w : ℝ → ℝ) (ξ X : ℝ) (t : ℝ) : ℂ :=
  oscillatoryTest w ξ (t / X)

noncomputable def scaledOscillatoryTestDeriv (w w' : ℝ → ℝ) (ξ X : ℝ) (t : ℝ) : ℂ :=
  oscillatoryTestDeriv w w' ξ (t / X) / (X : ℂ)

theorem hasDerivAt_scaledOscillatoryTest {w w' : ℝ → ℝ} {ξ X t : ℝ}
    (hw : HasDerivAt w (w' (t / X)) (t / X)) :
    HasDerivAt (scaledOscillatoryTest w ξ X)
      (scaledOscillatoryTestDeriv w w' ξ X t) t := by
  have h := (hasDerivAt_oscillatoryTest (ξ := ξ) hw).scomp t ((hasDerivAt_id t).div_const X)
  change HasDerivAt (fun s => oscillatoryTest w ξ (s / X)) _ t
  simpa only [scaledOscillatoryTestDeriv,
    oscillatoryTestDeriv, Function.comp_def, id_eq, one_div, one_mul, Complex.real_smul,
    Complex.ofReal_inv, div_eq_mul_inv, mul_comm (X : ℂ)⁻¹] using! h

theorem scaledOscillatoryTest_norm_le {w : ℝ → ℝ} {M ξ X t : ℝ}
    (hw : |w (t / X)| ≤ M) : ‖scaledOscillatoryTest w ξ X t‖ ≤ M := by
  simpa only [scaledOscillatoryTest, oscillatoryTest_norm] using hw

theorem scaledOscillatoryTestDeriv_norm_le {w w' : ℝ → ℝ} {M N ξ X t : ℝ}
    (hX : 0 < X) (hw : |w (t / X)| ≤ M) (hw' : |w' (t / X)| ≤ N) :
    ‖scaledOscillatoryTestDeriv w w' ξ X t‖ ≤ (N + 2 * Real.pi * |ξ| * M) / X := by
  simp only [scaledOscillatoryTestDeriv, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hX]
  apply div_le_div_of_nonneg_right _ hX.le
  exact (oscillatoryTestDeriv_norm_le w w' ξ (t / X)).trans
    (add_le_add hw' (mul_le_mul_of_nonneg_left hw (by positivity)))

theorem scaledOscillatoryTestDeriv_continuous {w w' : ℝ → ℝ}
    (hw : Continuous w) (hw' : Continuous w') (ξ X : ℝ) :
    Continuous (scaledOscillatoryTestDeriv w w' ξ X) := by
  have hc := oscillatoryTestDeriv_continuousOn hw.continuousOn hw'.continuousOn ξ
    (s := Set.univ)
  have hglobal := continuousOn_univ.mp hc
  exact (hglobal.comp (continuous_id.div_const X)).div_const _

theorem scaledOscillatoryTest_integral (w : ℝ → ℝ) (ρ : ℝ → ℂ)
    (ξ a b X : ℝ) (hX : X ≠ 0) :
    (∫ t in a * X..b * X, scaledOscillatoryTest w ξ X t * ρ t) =
      (X : ℂ) * ∫ s in a..b, oscillatoryTest w ξ s * ρ (s * X) := by
  have h := intervalIntegral.smul_integral_comp_mul_right
    (fun t => scaledOscillatoryTest w ξ X t * ρ t) (a := a) (b := b) X
  simpa only [scaledOscillatoryTest, mul_div_cancel_right₀ _ hX, Complex.real_smul] using h.symm

end JointDickman

end OAI
