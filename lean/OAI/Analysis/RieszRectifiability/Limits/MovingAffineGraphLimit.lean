import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NormalizedNormalCoordinates
import OAI.Analysis.RieszRectifiability.Flatness.AssembledAffineHeight
import OAI.Analysis.RieszRectifiability.Flatness.AffineGraphExcess
import OAI.Analysis.RieszRectifiability.Kernel.LipschitzRetractionError
import OAI.Analysis.RieszRectifiability.Limits.VectorStrongLimitStability

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped NNReal

theorem moving_affine_graph_distance_tendsto_zero {n q d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (a : ℕ → Ambient d)
    (L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d) (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d)
    (horth : ∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0)
    (hsplit : ∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
      N j ((N j).toContinuousLinearMap.adjoint y) = y)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (b : Ambient q) (B : Ambient d →L[ℝ] Ambient q)
    (hraw : ∀ j, Integrable (fun x => ‖normalizedNormalHeight (a j) (N j) (δ j) x‖ ^ 2) (μ j))
    (C : ℝ) (hC : ∀ j, (∫ x, ‖normalizedNormalHeight (a j) (N j) (δ j) x‖ ^ 2 ∂μ j) ≤ C)
    (herr : ∀ j, Integrable
      (fun x => ‖normalizedNormalHeight (a j) (N j) (δ j) x - (b + B x)‖ ^ 2) (μ j))
    (hstrong : Tendsto (fun j => ∫ x,
      ‖normalizedNormalHeight (a j) (N j) (δ j) x - (b + B x)‖ ^ 2 ∂μ j) atTop (𝓝 0)) :
    ∃ S : ℕ → AffineSubspace ℝ (Ambient d),
      (∀ j, (S j : Set (Ambient d)).Nonempty ∧ Module.finrank ℝ (S j).direction = n) ∧
      (∀ j, Integrable (fun x => (infDist x (S j : Set (Ambient d)) / δ j) ^ 2) (μ j)) ∧
      Tendsto (fun j => ∫ x, (infDist x (S j : Set (Ambient d)) / δ j) ^ 2 ∂μ j)
        atTop (𝓝 0) := by
  let w := fun j => normalizedNormalHeight (a j) (N j) (δ j)
  let P := fun j => tangentPlaneProjection (a j) (L j)
  let v := fun x => b + B x
  have hwm : ∀ j, Measurable (w j) :=
    fun j => (normalizedNormalHeight_continuous (a j) (N j) (δ j)).measurable
  have hPm : ∀ j, Measurable (P j) :=
    fun j => (tangentPlaneProjection_continuous (a j) (L j)).measurable
  have hv : LipschitzWith ‖B‖₊ v := vectorAffine_lipschitz b B
  have hvm : Measurable v := hv.continuous.measurable
  have hphysical : ∀ j, ∀ᵐ x ∂μ j, dist x (P j x) ≤ δ j * ‖w j x‖ := by
    intro j
    exact Eventually.of_forall fun x =>
      (physical_projection_distance_eq (a j) (L j) (N j) (hsplit j) (δ j) (hδ j) x).le
  have hproj : ∀ j, Integrable (fun x => ‖v x - v (P j x)‖ ^ 2) (μ j) :=
    fun j => (lipschitz_retraction_error_integral_bound (μ j) v ‖B‖₊ hv (P j) (hPm j)
      (δ j) (hδ j).le (w j) (hraw j) (hphysical j)).1
  have hprojlim := lipschitz_retraction_error_tendsto_zero μ v ‖B‖₊ hv P hPm δ
    (fun j => (hδ j).le) hδlim w hraw hphysical C hC
  have hi : ∀ j, Integrable (fun x => ‖w j x - v (P j x)‖ ^ 2) (μ j) :=
    fun j => (vector_error_integrable_and_bound (μ j) (w j) v (fun x => v (P j x))
      (hwm j) (hvm.comp (hPm j)) (herr j) (hproj j)).1
  have hlim := vector_strong_limit_trans μ w (fun _ => v) (fun j x => v (P j x))
    hwm (fun j => hvm.comp (hPm j)) herr hproj hstrong hprojlim
  let c := fun j => b + B (a j)
  let A := fun j => B.comp (L j).toContinuousLinearMap
  let t := fun j x => (L j).toContinuousLinearMap.adjoint (x - a j)
  have heq : ∀ j x, v (P j x) = c j + A j (t j x) := by
    intro j x
    change b + B (a j + L j ((L j).toContinuousLinearMap.adjoint (x - a j))) =
      (b + B (a j)) + B (L j ((L j).toContinuousLinearMap.adjoint (x - a j)))
    rw [map_add, add_assoc]
  let S := fun j => affineGraphPlane (a j) (L j) (N j) (c j) (A j) (δ j)
  have hg : ∀ j,
      Integrable (fun x => (infDist x (S j : Set (Ambient d)) / δ j) ^ 2) (μ j) ∧
      (∫ x, (infDist x (S j : Set (Ambient d)) / δ j) ^ 2 ∂μ j) ≤
        ∫ x, ‖w j x - v (P j x)‖ ^ 2 ∂μ j := by
    intro j
    have hi' : Integrable (fun x => ‖w j x - (c j + A j (t j x))‖ ^ 2) (μ j) := by
      simpa only [heq] using! hi j
    have h := affineGraphPlane_integral_normalized_distance_sq_le (μ j) (a j) (L j) (N j)
      (c j) (A j) (δ j) (hδ j) (t j) (w j)
      (Eventually.of_forall fun x => normal_coordinates_decomposition (a j) (L j) (N j)
        (hsplit j) (δ j) (hδ j).ne' x) hi'
    simpa only [heq] using! h
  refine ⟨S, ?_, fun j => (hg j).1, ?_⟩
  · intro j
    exact ⟨AffineSubspace.mk'_nonempty _ _,
      affineGraphPlane_direction_finrank (a j) (L j) (N j) (c j) (A j) (δ j) (horth j)⟩
  · exact squeeze_zero (fun j => integral_nonneg fun x => sq_nonneg _)
      (fun j => (hg j).2) hlim

end

end RieszRectifiability

end OAI
