import Mathlib.Order.Interval.Set.Infinite
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothTruncatedContour

namespace OAI

/-! # Heights at which the character contour crosses no zero -/

namespace Ostmann

open Set

theorem PrimitiveComplexCharacter.exists_contour_height (χ : PrimitiveComplexCharacter)
    (T : ℝ) : ∃ t : ℝ, T < t ∧ t < T + 1 ∧
      ∀ z ∈ complexCharacterZeros χ, |z.im| ≠ t := by
  let A := {z : ℂ | z ∈ complexCharacterZeros χ ∧ |z.im| ≤ T + 1}
  have hA : A.Finite := χ.strip_zeros_finite (T + 1)
  obtain ⟨t, ht, hnot⟩ := (Set.Ioo_infinite (show T < T + 1 by linarith)).exists_notMem_finite
    (hA.image (fun z : ℂ => |z.im|))
  refine ⟨t, ht.1, ht.2, ?_⟩
  intro z hz he
  apply hnot
  exact ⟨z, ⟨hz, by rw [he]; exact ht.2.le⟩, he⟩

end Ostmann

end OAI
