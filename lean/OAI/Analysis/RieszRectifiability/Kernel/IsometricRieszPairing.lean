import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.PlanarPullbackMeasure
import OAI.Analysis.RieszRectifiability.Kernel.RieszPairingIdentification

namespace OAI

/-!
# Isometric transport of Riesz pairings

Linear isometries intertwine the Riesz kernel and preserve its scalar interior
and far-field integrands. Pulling back balls and closed exteriors then transports
the corresponding scalar pairing to the lower-dimensional ambient space.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem kernel_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (x y : Ambient n) :
    kernel m (L x) (L y) = L (kernel m x y) := by
  simp only [kernel, ← map_sub, L.norm_map, map_smul]

theorem rieszInteriorIntegrand_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (e : Ambient n) (φ : Ambient d → ℝ)
    (q : Ambient n × Ambient n) :
    rieszInteriorIntegrand m (L e) φ (L q.1, L q.2) =
      rieszInteriorIntegrand m e (fun x => φ (L x)) q := by
  simp only [rieszInteriorIntegrand, kernel_linearIsometry, L.inner_map_map]

theorem rieszFarIntegrand_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (e a : Ambient n) (φ : Ambient d → ℝ)
    (q : Ambient n × Ambient n) :
    rieszFarIntegrand m (L e) φ (L a) (L q.1, L q.2) =
      rieszFarIntegrand m e (fun x => φ (L x)) a q := by
  simp only [rieszFarIntegrand, kernel_linearIsometry, ← map_sub, L.inner_map_map]

theorem linearIsometry_pair_integral {n d : ℕ}
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n)) [SFinite μ]
    (A B : Set (Ambient d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (F : Ambient d × Ambient d → ℝ) :
    (∫ q, F q ∂((μ.map L).restrict A).prod ((μ.map L).restrict B)) =
      ∫ q : Ambient n × Ambient n, F (L q.1, L q.2)
        ∂(μ.restrict (L ⁻¹' A)).prod (μ.restrict (L ⁻¹' B)) := by
  rw [Measure.restrict_map L.continuous.measurable hA,
    Measure.restrict_map L.continuous.measurable hB,
    Measure.map_prod_map _ _ L.continuous.measurable L.continuous.measurable]
  exact (L.isometry.isClosedEmbedding.measurableEmbedding.prodMap
    L.isometry.isClosedEmbedding.measurableEmbedding).integral_map F

theorem rieszScalarPairing_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n)) [SFinite μ]
    (a : Ambient n) (R : ℝ) (e : Ambient n) (φ : Ambient d → ℝ) :
    rieszScalarPairing m (μ.map L) (L a) R (L e) φ =
      rieszScalarPairing m μ a R e (fun x => φ (L x)) := by
  have hball : L ⁻¹' ball (L a) R = ball a R := by
    ext x
    simp only [mem_preimage, mem_ball, L.dist_map]
  have hext : L ⁻¹' closedExterior (L a) R = closedExterior a R := by
    ext x
    simp only [mem_preimage, closedExterior, mem_ofPred_eq, L.dist_map]
  unfold rieszScalarPairing
  dsimp only
  rw [linearIsometry_pair_integral L μ (ball (L a) R) (ball (L a) R)
      measurableSet_ball measurableSet_ball,
    linearIsometry_pair_integral L μ (ball (L a) R) (closedExterior (L a) R)
      measurableSet_ball (closedExterior_measurable (L a) R)]
  simp only [hball, hext, rieszInteriorIntegrand_linearIsometry,
    rieszFarIntegrand_linearIsometry]

end

end RieszRectifiability

end OAI
