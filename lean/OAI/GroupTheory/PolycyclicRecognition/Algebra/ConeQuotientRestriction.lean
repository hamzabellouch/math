import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorQuotientAction

namespace OAI

/-! # Transporting the first quotient restriction to a tile's frame -/

namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {N D G Q : Type*} [Group N] [Group D] [Group G] [Group Q]

/-- The quotient orbit point is independent of the chosen overlapping
factorization of the ambient element. -/
theorem quotient_lift_coordinate
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ n d q, act (ι n * κ d) q = π n * α d q)
    (n : N) (d : D) : act (ι n * κ d) 1 = π n := by
  rw [hact, map_one, mul_one]

/-- A first-sheet quotient bound becomes a translated automorphic image
in the second-sheet frame. The translation may have arbitrary size. -/
theorem quotient_restriction_in_anchor_frame
    (ι : N →* G) (κ : D →* G) (π : N →* Q)
    (α : D →* MulAut Q) (act : G →* Equiv.Perm Q)
    (hact : ∀ n d q, act (ι n * κ d) q = π n * α d q)
    (base anchor endpoint : G) (u n₀ : N) (d d₀ : D)
    (hlift : anchor⁻¹ * endpoint = ι u * κ d)
    (hframe : anchor⁻¹ * base = ι n₀ * κ d₀)
    (T : Set Q) (hfirst : act (base⁻¹ * endpoint) 1 ∈ T) :
    π u ∈ π n₀ • (α d₀ '' T) := by
  have heq : act (anchor⁻¹ * endpoint) 1 =
      act (anchor⁻¹ * base) (act (base⁻¹ * endpoint) 1) := by
    rw [← Equiv.Perm.mul_apply, ← map_mul]
    simp [mul_assoc]
  rw [hlift, quotient_lift_coordinate ι κ π α act hact, hframe, hact] at heq
  rw [heq]
  exact ⟨α d₀ (act (base⁻¹ * endpoint) 1),
    ⟨act (base⁻¹ * endpoint) 1, hfirst, rfl⟩, rfl⟩

end PolycyclicRecognition

end OAI
