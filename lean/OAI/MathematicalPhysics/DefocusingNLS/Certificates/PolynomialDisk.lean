import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ParameterOpenness
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

namespace OAI

/-!
# A finite root certificate on a complex disk

Brouwer degree gives a root of a degree-fifteen polynomial in a prescribed
disk when the constant and higher-order terms are bounded by the linear term.
-/

open Metric

namespace DefocusingNLS

/-- A degree-fifteen polynomial has a zero in a disk if its constant and
higher-order terms are uniformly smaller than its linear term there. -/
theorem degree_fifteen_root_in_disk (a b : ℂ) (c : Fin 14 → ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hb : b ≠ 0)
    (hbound : ‖a‖ + ∑ i, ‖c i‖ * r ^ ((i : ℕ) + 2) ≤ ‖b‖ * r) :
    ∃ z : ℂ, ‖z‖ ≤ r ∧ a + b * z + ∑ i, c i * z ^ ((i : ℕ) + 2) = 0 := by
  let tail : ℂ → ℂ := fun z => ∑ i, c i * z ^ ((i : ℕ) + 2)
  let f : closedBall (0 : ℂ) r → ℂ := fun z => z.val + (a + tail z) / b
  have hf : Continuous f := by
    dsimp [f, tail]
    fun_prop
  have herror (z : closedBall (0 : ℂ) r) : ‖f z - z.val‖ ≤ r := by
    have hz : ‖z.val‖ ≤ r := by
      have hz := z.property
      change dist z.val 0 ≤ r at hz
      simpa only [dist_zero_right] using hz
    have htail : ‖tail z‖ ≤ ∑ i, ‖c i‖ * r ^ ((i : ℕ) + 2) := by
      calc
        ‖tail z‖ ≤ ∑ i, ‖c i * z.val ^ ((i : ℕ) + 2)‖ := norm_sum_le _ _
        _ ≤ ∑ i, ‖c i‖ * r ^ ((i : ℕ) + 2) := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_mul, norm_pow]
          gcongr
    calc
      ‖f z - z.val‖ = ‖a + tail z‖ / ‖b‖ := by simp [f]
      _ ≤ (‖a‖ + ∑ i, ‖c i‖ * r ^ ((i : ℕ) + 2)) / ‖b‖ :=
        div_le_div_of_nonneg_right ((norm_add_le _ _).trans (add_le_add le_rfl htail))
          (norm_nonneg _)
      _ ≤ r := (div_le_iff₀ (norm_pos_iff.mpr hb)).mpr (by nlinarith [hbound])
  obtain ⟨z, hz⟩ := zero_of_small_continuous_error r r hr le_rfl f hf herror
  refine ⟨z, ?_, ?_⟩
  · have hz := z.property
    change dist z.val 0 ≤ r at hz
    simpa only [dist_zero_right] using hz
  change z.val + (a + tail z) / b = 0 at hz
  change a + b * z.val + tail z = 0
  calc
    a + b * z.val + tail z = b * (z.val + (a + tail z) / b) := by
      field_simp [hb]
      ring
    _ = 0 := by rw [hz, mul_zero]

end DefocusingNLS

end OAI
