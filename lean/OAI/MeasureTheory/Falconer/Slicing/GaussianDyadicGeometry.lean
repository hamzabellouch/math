import OAI.MeasureTheory.Falconer.Slicing.OrientedSliceBalls
import OAI.MeasureTheory.Falconer.Slicing.SliceScaling

namespace OAI

/-! # The dyadic tests controlling scaled point and normalized direction balls -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {ι : Type*}

theorem gaussian_scaled_point_test
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K L a u : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (ha : 0 < a) (hu : 0 < u)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (haK : 4*L+2*K*(h:ℝ) ≤ a) (hδ : δ ≤ u/(2*a)) (hr : r i = u/2) (c : Space m) :
    ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z)))
      {x | dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ u/(2*a)} ≤ TP i := by
  have hs : 0 < u/(2*a) := by positivity
  have he : a*(u/(2*a)) = u/2 := by field_simp
  have h₁ := mul_le_mul_of_nonneg_right haK hs.le
  have h₂ := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 2*K*(h:ℝ))
  have hrad : 4*(L*(u/(2*a)))+K*((h:ℝ)*(2*δ)) ≤ r i := by
    rw [hr]
    nlinarith
  apply (measure_mono (show
    {x | dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ u/(2*a)} ⊆
    {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) (L • c) ≤ L*(u/(2*a))} from ?_)).trans
      (gaussian_pruned_oriented_point_closed_ball μ A z e δ r TP i hK (mul_pos hL hs) hbound hrad _)
  intro x hx
  change dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ u/(2*a) at hx
  rw [slice_scaled_distance hL,mul_comm,← div_eq_mul_inv] at hx
  change dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) (L • c) ≤ L*(u/(2*a))
  simpa only [mul_comm] using (div_le_iff₀ hL).mp hx

theorem gaussian_normalized_direction_test
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TD : ι → ℝ≥0∞) (M : ℝ≥0∞) (i : ι)
    {K a u : ℝ} (hK : 0 ≤ K) (ha : 0 < a) (hu : 0 < u)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (haK : 4+4*K*(h:ℝ) ≤ a)
    (hδ : δ ≤ u/(2*a)) (hr : r i = u/2) (c : Space m) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A))
      {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ u/(2*a)} ≤ TD i := by
  have hs : 0 < u/(2*a) := by positivity
  have he : a*(u/(2*a)) = u/2 := by field_simp
  have h₁ := mul_le_mul_of_nonneg_right haK hs.le
  have h₂ := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 4*K*(h:ℝ))
  have hrad : 4*(u/(2*a))+4*(K*((h:ℝ)*δ)) ≤ r i := by
    rw [hr]
    nlinarith
  exact gaussian_pruned_oriented_direction_closed_ball ν A e δ r TD M i hK hs hbound hsmall hrad c

end Falconer

end OAI
