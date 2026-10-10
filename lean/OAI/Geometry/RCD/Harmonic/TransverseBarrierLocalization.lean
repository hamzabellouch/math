import OAI.Geometry.RCD.Harmonic.TransverseBarrierLower

namespace OAI

/-! # A supporting halfspace localizes the positive transverse test -/

open scoped InnerProductSpace
namespace RegularPointCoordinates

theorem transverse_barrier_localization {n : ℕ} (z a : Euclidean n) {δ d : ℝ}
    (hδ : 0<δ) (hd : d≤‖z‖+δ) (hsupport : ⟪z,a⟫_ℝ≤δ)
    (hW : -δ<⟪z,a⟫_ℝ) (hS : ‖z‖^2-⟪z,a⟫_ℝ^2<δ^2) : d<3*δ := by
  have hw : ⟪z,a⟫_ℝ^2≤δ^2 := by nlinarith
  have hz : ‖z‖<2*δ := by nlinarith [norm_nonneg z]
  linarith

end RegularPointCoordinates

end OAI
