import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.End

namespace OAI

/-! # The three actual endpoints used in the cone offset comparison -/

namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {N : Type*} [Group N]

/-- The endpoint carrying both the ideal probe and its quotient section. -/
def coneProbeFirst (S : MulAut N) (n i s : N) : N := n * S (i * s)

/-- The neighboring endpoint carrying the same ideal probe. -/
def coneProbeSecond (S : MulAut N) (n i k : N) : N := n * S i * S k

/-- The bridge is independent of the ideal probe. -/
theorem coneProbe_bridge (S : MulAut N) (n i s k : N) :
    (coneProbeFirst S n i s)⁻¹ * coneProbeSecond S n i k = S (s⁻¹ * k) := by
  simp [coneProbeFirst, coneProbeSecond, map_mul, mul_assoc]

/-- The path from the neighboring sheet to a tile anchor is the reverse
conjugate of that anchor. -/
theorem coneProbe_anchor_increment (S : MulAut N) (n a k : N) :
    (n * S k)⁻¹ * coneProbeSecond S n a k = S (k⁻¹ * a * k) := by
  simp [coneProbeSecond, map_mul, mul_assoc]

/-- Within one tile the second-sheet increment is exactly its conjugated
ideal coordinate. -/
theorem coneProbe_tile_increment (S : MulAut N) (n a i k : N) :
    (coneProbeSecond S n a k)⁻¹ * coneProbeSecond S n i k =
      S (k⁻¹ * a⁻¹ * i * k) := by
  simp [coneProbeSecond, map_mul, mul_assoc]

/-- The covering inclusion gives the required small ideal increment
without a condition on the quotient-section coordinate. -/
theorem coneProbe_tile_increment_mem (S : MulAut N) (n a i k : N) (B : Set N)
    (hi : i ∈ (fun z => a * k * z * k⁻¹) '' B) :
    (coneProbeSecond S n a k)⁻¹ * coneProbeSecond S n i k ∈ S '' B := by
  obtain ⟨z, hz, rfl⟩ := hi
  rw [coneProbe_tile_increment]
  refine ⟨z, hz, ?_⟩
  simp [mul_assoc]

end PolycyclicRecognition

end OAI
