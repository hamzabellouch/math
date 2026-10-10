import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Injectivity on convex patches with controlled derivative oscillation -/

namespace PolycyclicRecognition

open Set

theorem injOn_of_derivative_oscillation
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : V → W) (df : V → V →L[ℝ] W) (A : V →L[ℝ] W)
    {S : Set V} (hS : Convex ℝ S)
    (hf : ∀ x ∈ S, HasFDerivAt f (df x) x)
    {η D ε : ℝ} (hD : 0 ≤ D) (hgap : D * ε < η)
    (hA : ∀ v, η * ‖v‖ ≤ D * ‖A v‖)
    (hosc : ∀ x ∈ S, ‖df x - A‖ ≤ ε) : Set.InjOn f S := by
  intro x hx y hy hxy
  have he := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => f z - A z) (f' := fun z => df z - A)
    (fun z hz => ((hf z hz).sub A.hasFDerivAt).hasFDerivWithinAt)
    hosc hx hy
  have hn : ‖A (y - x)‖ ≤ ε * ‖y - x‖ := by
    rw [map_sub, norm_sub_rev]
    simpa only [hxy, sub_sub_sub_cancel_left] using he
  have hb := (hA (y - x)).trans (mul_le_mul_of_nonneg_left hn hD)
  have hz : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end PolycyclicRecognition

end OAI
