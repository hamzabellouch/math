import OAI.GroupTheory.PolycyclicRecognition.Analysis.FactorProductVolumeBound
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # A common separated-point bound for all probe tiles

The product lifts need not be unique. The proved lifted-cell packing
inequality and common volume envelopes give one loss for every tile.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

variable {N D G : Type*} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MeasurableSpace D] [MeasurableMul N] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]

/-- The per-tile exponent survives passage from containing product
regions to separated projected endpoints, uniformly over all tiles. -/
theorem sequence_tile_separated_count
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (μ : Measure N) (ν : Measure D) [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    [SFinite μ] [SFinite ν] (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (tiles : ℕ → ℕ) (s : ∀ n, Fin (tiles n) → Finset G)
    (p : ∀ n, Fin (tiles n) → G → N × D)
    (E : ∀ n, Fin (tiles n) → Set N) (B : ℕ → Set D)
    (U : Set (N × D)) (hU : MeasurableSet U)
    (hU0 : (μ.prod ν) U ≠ 0) (hUtop : (μ.prod ν) U ≠ ⊤)
    (hE : ∀ n j, μ (E n j) ≠ ⊤) (hB : ∀ n, ν (B n) ≠ ⊤) {ρ : ℝ}
    (hp : ∀ n j, ∀ x ∈ s n j, ι (p n j x).1 * κ (p n j x).2 = x)
    (hsmall : ∀ z ∈ U, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hsep : ∀ n j, ∀ x ∈ s n j, ∀ y ∈ s n j, x ≠ y → ρ ≤ dist x y)
    (hthick : ∀ n j, ∀ x ∈ s n j, factorTranslate φ (p n j x) '' U ⊆ E n j ×ˢ B n)
    (A Bvol : ℕ → ℝ)
    (hA : HasSubexponentialUpperBoundSeq scale A)
    (hBvol : HasSubexponentialUpperBoundSeq scale Bvol)
    (hA0 : ∀ n, 0 ≤ A n) (hBvol0 : ∀ n, 0 ≤ Bvol n)
    (P ell : ℝ)
    (hNvol : ∀ n j, (μ (E n j)).toReal ≤ A n * Real.exp ((P - ell) * scale n))
    (hDvol : ∀ n, (ν (B n)).toReal ≤ Bvol n) :
    ∃ loss : ℕ → ℝ, HasSubexponentialUpperBoundSeq scale loss ∧
      (∀ n, 0 ≤ loss n) ∧ ∀ n j,
        ((s n j).card : ℝ) ≤ loss n * Real.exp ((P - ell) * scale n) := by
  let c := ((μ.prod ν) U).toReal
  have hc0 : 0 < c := ENNReal.toReal_pos hU0 hUtop
  let loss := fun n => A n * Bvol n * c⁻¹
  have hloss : HasSubexponentialUpperBoundSeq scale loss :=
    (hA.mul hBvol (Eventually.of_forall hA0)).mul
      (sequence_subexponential_upper_const hscale c⁻¹)
      (Eventually.of_forall (fun n => mul_nonneg (hA0 n) (hBvol0 n)))
  refine ⟨loss, hloss,
    fun n => mul_nonneg (mul_nonneg (hA0 n) (hBvol0 n)) (inv_nonneg.mpr hc0.le), ?_⟩
  intro n j
  have hcount := factor_separated_card_le_product_volume φ ι κ hc μ ν hφ
    (s n j) (p n j) U (E n j) (B n) hU hU0 hUtop (hE n j) (hB n)
    (hp n j) hsmall (hsep n j) (hthick n j)
  calc
    _ ≤ (μ (E n j)).toReal * (ν (B n)).toReal / c := hcount
    _ ≤ (A n * Real.exp ((P - ell) * scale n)) * Bvol n / c := by
      apply div_le_div_of_nonneg_right _ hc0.le
      exact mul_le_mul (hNvol n j) (hDvol n) ENNReal.toReal_nonneg
        (mul_nonneg (hA0 n) (Real.exp_pos _).le)
    _ = loss n * Real.exp ((P - ell) * scale n) := by dsimp [loss]; ring

end PolycyclicRecognition

end

end OAI
