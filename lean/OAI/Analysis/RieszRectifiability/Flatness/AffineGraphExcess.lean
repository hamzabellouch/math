import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.AffineGraphPlane

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Topology

theorem affineGraphPlane_normalized_distance_sq_le {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (b : Ambient q) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ) (hδ : 0 < δ)
    (x : Ambient d) (t : Ambient n) (w : Ambient q) (hx : x - a = L t + δ • N w) :
    (infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ) ^ 2 ≤
      ‖w - (b + A t)‖ ^ 2 := by
  have hraw := affineGraphPlane_infDist_le a L N b A δ x t (δ • w)
    (by simpa only [map_smul] using! hx)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hδ] at hraw
  have hb : infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ ≤
      ‖w - (b + A t)‖ :=
    (div_le_iff₀ hδ).mpr (by simpa only [mul_comm] using! hraw)
  exact (sq_le_sq₀ (div_nonneg infDist_nonneg hδ.le) (norm_nonneg _)).mpr hb

theorem affineGraphPlane_integral_normalized_distance_sq_le {n q d : ℕ}
    (μ : Measure (Ambient d)) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (b : Ambient q) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ) (hδ : 0 < δ)
    (t : Ambient d → Ambient n) (w : Ambient d → Ambient q)
    (hx : ∀ᵐ x ∂μ, x - a = L (t x) + δ • N (w x))
    (hi : Integrable (fun x => ‖w x - (b + A (t x))‖ ^ 2) μ) :
    Integrable (fun x =>
      (infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ) ^ 2) μ ∧
    (∫ x, (infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ) ^ 2 ∂μ) ≤
      ∫ x, ‖w x - (b + A (t x))‖ ^ 2 ∂μ := by
  have hb : ∀ᵐ x ∂μ,
      (infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ) ^ 2 ≤
        ‖w x - (b + A (t x))‖ ^ 2 := by
    filter_upwards [hx] with x hx
    exact affineGraphPlane_normalized_distance_sq_le a L N b A δ hδ x (t x) (w x) hx
  have hm : AEStronglyMeasurable (fun x =>
      (infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ) ^ 2) μ :=
    (((continuous_infDist_pt _).div_const δ).pow 2).aestronglyMeasurable
  have hi' := hi.mono' hm (hb.mono fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg
      (infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ))]
    exact hx)
  exact ⟨hi', integral_mono_ae hi' hi hb⟩

end

end RieszRectifiability

end OAI
