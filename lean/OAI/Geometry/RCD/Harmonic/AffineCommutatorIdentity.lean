import OAI.Geometry.RCD.Harmonic.TwoCenterCommutator
import Mathlib.Tactic.Module

namespace OAI

/-! # The affine coefficient identity behind the two-center commutator

Here U is the centered coordinate column, G its radial derivative at z,
H the difference of the two radial derivatives, and C the constant part
of the affine approximation to H. D and V are the actual radial derivative
maps; J is restriction to the common L2 region.
-/

noncomputable section
namespace RegularPointCoordinates

variable {E F W : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup W] [Module ℝ W]

/-- The coefficient expression is a sum of the genuine commutator error
and the four value/gradient errors of the two radial approximations. -/
theorem affine_commutator_identity
    (A B : Module.End ℝ E) (U G H C : E →ₗ[ℝ] F) (D V J : F →ₗ[ℝ] W)
    (hDU : ∀ a, D (U a) = J (G a))
    (hVU : ∀ a, V (U a) = J (H a))
    (hDC : ∀ a, D (C a) = 0) (b : E) :
    J (U ((A * B - B * (A - 1)) b)) - J (C ((A - 1) b)) =
      V (G b - U (A b)) - (V (G b) - D (H b) - J (H b)) -
        D (H b - U (B b) - C b) +
        J (H ((A - 1) b) - U (B ((A - 1) b)) - C ((A - 1) b)) -
        J (G (B b) - U (A (B b))) := by
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply,
    map_sub, hDU, hVU, hDC]
  module

section Norm
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The exact identity keeps the five analytic errors additive. No small
matrix term is absorbed before affine coefficient nondegeneracy is used. -/
theorem affine_commutator_error_bound
    (A B : Module.End ℝ E) (U G H C : E →ₗ[ℝ] F) (D V J : F →ₗ[ℝ] Y)
    (hDU : ∀ a, D (U a) = J (G a))
    (hVU : ∀ a, V (U a) = J (H a))
    (hDC : ∀ a, D (C a) = 0) (b : E)
    {e₁ e₂ e₃ e₄ e₅ : ℝ}
    (h₁ : ‖V (G b - U (A b))‖ ≤ e₁)
    (h₂ : ‖V (G b) - D (H b) - J (H b)‖ ≤ e₂)
    (h₃ : ‖D (H b - U (B b) - C b)‖ ≤ e₃)
    (h₄ : ‖J (H ((A - 1) b) - U (B ((A - 1) b)) - C ((A - 1) b))‖ ≤ e₄)
    (h₅ : ‖J (G (B b) - U (A (B b)))‖ ≤ e₅) :
    ‖J (U ((A * B - B * (A - 1)) b)) - J (C ((A - 1) b))‖ ≤
      e₁ + e₂ + e₃ + e₄ + e₅ := by
  rw [affine_commutator_identity A B U G H C D V J hDU hVU hDC b]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add h₁ h₂)) h₃)) h₄)) h₅)

end Norm
end RegularPointCoordinates

end

end OAI
