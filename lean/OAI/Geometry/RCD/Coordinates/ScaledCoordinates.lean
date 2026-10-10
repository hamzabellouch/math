import OAI.Geometry.RCD.Metric.RecenterApproximation
import OAI.Geometry.RCD.Harmonic.TransformedColumns

namespace OAI

/-! # Invertible coordinate normalization with physical scale included -/

open Metric
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

/-- Include the physical inverse radius in the invertible coordinate change. -/
def scaledCoordinateEquiv {n : ℕ} (A : Euclidean n ≃L[ℝ] Euclidean n)
    (c : ℝ) (hc : c ≠ 0) : Euclidean n ≃L[ℝ] Euclidean n :=
  A.trans (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 c hc))

theorem scaledCoordinateEquiv_toCLM {n : ℕ} (A : Euclidean n ≃L[ℝ] Euclidean n)
    (c : ℝ) (hc : c ≠ 0) :
    (scaledCoordinateEquiv A c hc : Euclidean n →L[ℝ] Euclidean n) =
      c • (A : Euclidean n →L[ℝ] Euclidean n) := by
  ext x
  rfl

theorem scaledCoordinateEquiv_adjoint {n : ℕ} (A : Euclidean n ≃L[ℝ] Euclidean n)
    (c : ℝ) (hc : c ≠ 0) (z : Euclidean n) :
    (scaledCoordinateEquiv A c hc : Euclidean n →L[ℝ] Euclidean n).adjoint z =
      c • (A : Euclidean n →L[ℝ] Euclidean n).adjoint z := by
  rw [scaledCoordinateEquiv_toCLM, map_smulₛₗ]
  simp only [starRingEnd_apply, star_trivial, smul_apply]

theorem centered_scaledCoordinateEquiv {X : Type*} {n : ℕ}
    (v : X → Euclidean n) (p x : X) (A : Euclidean n ≃L[ℝ] Euclidean n)
    (c : ℝ) (hc : c ≠ 0) :
    (scaledCoordinateEquiv A c hc : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
      (scaledCoordinateEquiv A c hc : Euclidean n →L[ℝ] Euclidean n).adjoint (v p) =
      c • ((A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
        (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v p)) := by
  rw [scaledCoordinateEquiv_adjoint, scaledCoordinateEquiv_adjoint, smul_sub]

/-- The normalization at radius four times the testing radius gives the
radius-two metric approximation needed for harmonic compactness. -/
theorem normalized_approximation_rescale_four {X : Type*} [MetricSpace X] {n : ℕ}
    {p : X} {r ε : ℝ} (hr : 0 < r) (v : X → Euclidean n)
    (A : Euclidean n ≃L[ℝ] Euclidean n)
    (happ : IsPointedApproximation p 0 (4 * r) (1 / 2) ε
      (fun x => (4 * r)⁻¹ • ((A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
        (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v p)))) :
    IsPointedApproximation p 0 r 2 (4 * ε)
      (fun x =>
        (scaledCoordinateEquiv A r⁻¹ (inv_ne_zero hr.ne') : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
        (scaledCoordinateEquiv A r⁻¹ (inv_ne_zero hr.ne') : Euclidean n →L[ℝ] Euclidean n).adjoint (v p)) := by
  have he (x : X) : (4 : ℝ) • ((4 * r)⁻¹ •
      ((A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
        (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v p))) =
      (scaledCoordinateEquiv A r⁻¹ (inv_ne_zero hr.ne') : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
        (scaledCoordinateEquiv A r⁻¹ (inv_ne_zero hr.ne') : Euclidean n →L[ℝ] Euclidean n).adjoint (v p) := by
    rw [centered_scaledCoordinateEquiv, smul_smul]
    congr 1
    field_simp
  simpa only [he] using happ.rescale_four hr

end RegularPointCoordinates

end

end OAI
