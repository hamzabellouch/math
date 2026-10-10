import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ShellHeightL1
import OAI.Analysis.RieszRectifiability.Kernel.CutoffEnergyIntegral

namespace OAI

/-!
# Moments of squared-cutoff tests

A cutoff bounded by one preserves square-integrability when its square multiplies a test
function. Hölder integrability and pointwise domination then control the first moment of
this test and its pairing with the original function.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

theorem cutoff_square_le_one {X : Type*} (χ : X → ℝ)
    (hχ : ∀ x, |χ x| ≤ 1) (x : X) : χ x ^ 2 ≤ 1 := by
  simpa only [sq_abs, one_pow] using! pow_le_pow_left₀ (abs_nonneg (χ x)) (hχ x) 2

theorem squared_cutoff_test_memLp {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (w χ : X → ℝ) (hw : Measurable w) (hχ : Measurable χ)
    (hL2 : MemLp w 2 ν) (hbound : ∀ x, |χ x| ≤ 1) :
    MemLp (fun x => χ x ^ 2 * w x) 2 ν := by
  apply bounded_multiplier_memLp ν w (fun x => χ x ^ 2) hw (hχ.pow_const 2) hL2 1
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact cutoff_square_le_one χ hbound x

theorem squared_cutoff_test_moment_bounds {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (w χ : X → ℝ)
    (hw : Measurable w) (hχ : Measurable χ) (hL2 : MemLp w 2 ν) (hbound : ∀ x, |χ x| ≤ 1)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hmass : ν.real univ ≤ M) (hsecond : (∫ x, w x ^ 2 ∂ν) ≤ M * δ ^ 2) :
    Integrable (fun x => χ x ^ 2 * w x) ν ∧
      Integrable (fun x => (χ x ^ 2 * w x) * w x) ν ∧
      (∫ x, |χ x ^ 2 * w x| ∂ν) ≤ M * δ ∧
      (∫ x, |(χ x ^ 2 * w x) * w x| ∂ν) ≤ M * δ ^ 2 := by
  have htestL2 := squared_cutoff_test_memLp ν w χ hw hχ hL2 hbound
  have htest := htestL2.integrable (by norm_num)
  have hprodLp : MemLp (fun x => (χ x ^ 2 * w x) * w x) 1 ν := htestL2.mul hL2
  have hprod := memLp_one_iff_integrable.mp hprodLp
  refine ⟨htest, hprod, ?_, ?_⟩
  · calc
      _ ≤ ∫ x, |w x| ∂ν := by
        apply integral_mono htest.abs (hL2.integrable (by norm_num)).abs
        intro x
        change |χ x ^ 2 * w x| ≤ |w x|
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        simpa only [one_mul] using!
          mul_le_mul_of_nonneg_right (cutoff_square_le_one χ hbound x) (abs_nonneg (w x))
      _ ≤ _ := integral_abs_le_of_mass_second_moment ν w hL2 M δ hM hδ hmass hsecond
  · calc
      _ ≤ ∫ x, w x ^ 2 ∂ν := by
        apply integral_mono hprod.abs hL2.integrable_sq
        intro x
        change |(χ x ^ 2 * w x) * w x| ≤ w x ^ 2
        have heq : |(χ x ^ 2 * w x) * w x| = χ x ^ 2 * w x ^ 2 := by
          rw [mul_assoc, ← pow_two, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        rw [heq]
        simpa only [one_mul] using!
          mul_le_mul_of_nonneg_right (cutoff_square_le_one χ hbound x) (sq_nonneg (w x))
      _ ≤ _ := hsecond

end

end RieszRectifiability

end OAI
