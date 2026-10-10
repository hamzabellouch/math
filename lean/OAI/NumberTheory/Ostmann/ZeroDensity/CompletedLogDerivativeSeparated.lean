import OAI.NumberTheory.Ostmann.Characters.CharacterResolventBound
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterHadamardBounds

namespace OAI

/-! # The completed logarithmic derivative away from the actual zeros -/

namespace Ostmann

open Complex Filter
open scoped BigOperators Topology

theorem completed_logDeriv_difference_bound (χ : PrimitiveComplexCharacter)
    (s w : ℂ) (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hw : w.re = 2) (hshift : ‖w - s‖ ≤ A)
    (hsep : ∀ i : ℕ, δ ≤ ‖s - (actualCharacterZeros χ).zeros i‖) :
    ‖logDeriv χ.completed s - logDeriv χ.completed w‖ ≤
      A * (1 + A / δ) * characterRealZeroSum χ w := by
  have hsne : χ.completed s ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := actualCharacterZeros_complete χ s ((χ.completed_zero_iff s).mp hz)
    have hh := hsep i
    rw [hi, sub_self, norm_zero] at hh
    linarith
  have hwne : χ.completed w ≠ 0 := χ.completed_ne_zero_right w (by linarith)
  have hsum := character_real_zero_summable χ w (by linarith) (by linarith)
  have hbound (n : ℕ) :
      ‖completedZeroPartialFraction χ ((n : ℝ) + 1) s -
        completedZeroPartialFraction χ ((n : ℝ) + 1) w‖ ≤
          A * (1 + A / δ) * characterRealZeroSum χ w := by
    rw [completedZeroPartialFraction_index_sum χ (faithfulCharacterZeroEquiv χ),
      completedZeroPartialFraction_index_sum χ (faithfulCharacterZeroEquiv χ),
      ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ i ∈ (actualCharacterZeros χ).diskIndices ((n : ℝ) + 1),
          (A * (1 + A / δ)) * ((w - (actualCharacterZeros χ).zeros i)⁻¹).re := by
        apply Finset.sum_le_sum
        intro i _
        exact zero_resolvent_difference_bound s w _ A δ hA hδ (hsep i) hshift (by
          change 1 ≤ w.re - ((actualCharacterZeros χ).zeros i).re
          rw [hw]
          linarith [((actualCharacterZeros χ).in_strip i).2])
      _ ≤ A * (1 + A / δ) * characterRealZeroSum χ w := by
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hsum.sum_le_tsum _ (fun i _ => by
          rw [realZeroKernel_complex_sub]
          exact realZeroKernel_nonneg (by linarith [((actualCharacterZeros χ).in_strip i).2]))
  have hlim := (completed_partial_fraction_difference_tendsto χ w s hwne hsne).norm
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hbound)

end Ostmann

end OAI
