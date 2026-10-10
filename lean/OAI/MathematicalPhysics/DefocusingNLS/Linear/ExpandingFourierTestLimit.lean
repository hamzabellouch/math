import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFourierTest
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSmoothFilter
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPairingLimit
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalFourierTest

namespace OAI

/-! # Physical local limits determine all expanding Fourier test limits -/

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingFourierTest_physical (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (φ : 𝓢(E, ℂ)) (f : FourierL2) :
    expandingFourierTest a k L ha ha1 hk hL φ f =
      ∫ y : E, physicalFourierTest φ y * expandingPhysicalContinuous a k L ha ha1 hk hL f y := by
  have h := hasSum_periodicSchwartzPairing L (physicalFourierTest φ)
    (expandingFourierCoefficient a k L f)
    (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f)
  change (∑' n, expandingFourierCoefficient a k L f n * φ (L⁻¹ • (n : E))) =
    ∫ y : E, physicalFourierTest φ y *
      spatialFourierSeries (expandingFourierCoefficient a k L f) (L⁻¹ • y)
  simpa only [physicalFourierTest_kernel] using h.tsum_eq

theorem expandingFourierTest_tendsto_of_physical (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M) (v : HomogeneousY a k)
    (hp : ∀ y : E, Tendsto (fun n => expandingPhysicalContinuous a k (L n)
      ha ha1 hk (hL n) (f n) y) atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk v y)))
    (φ : 𝓢(E, ℂ)) :
    Tendsto (fun n => expandingFourierTest a k (L n) ha ha1 hk (hL n) φ (f n)) atTop
      (𝓝 ((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℂ) * homogeneousFourierPairing a k ha ha1 hk φ v)) := by
  have h := tendsto_schwartzPairing_of_bounded_pointwise (physicalFourierTest φ)
    (fun n => expandingPhysicalContinuous a k (L n) ha ha1 hk (hL n) (f n))
    (homogeneousPhysicalCLM a k ha ha1 hk v).toContinuousMap
    (expandingEmbeddingBound a k * M)
    (fun n y => (expandingPhysicalContinuous_norm_le a k (L n) ha ha1 hk (hL n) (f n) y).trans
      (mul_le_mul_of_nonneg_left (hf n) (by unfold expandingEmbeddingBound; positivity))) hp
  have he : (∫ y : E, physicalFourierTest φ y *
      (homogeneousPhysicalCLM a k ha ha1 hk v).toContinuousMap y) =
      (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℂ) * homogeneousFourierPairing a k ha ha1 hk φ v :=
    homogeneousFourierPairing_physical a k ha ha1 hk φ v
  rw [he] at h
  simpa only [← expandingFourierTest_physical] using h

end DefocusingNLS

end OAI
