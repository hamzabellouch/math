import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasurePacking
import Mathlib.Topology.MetricSpace.Defs

namespace OAI

/-! # From projected covers to lifted volume bounds

The mass over each projected ball includes every admissible auxiliary
coordinate. Consequently summing this mass over a cover does not require
the factor projection to be injective.
-/

namespace PolycyclicRecognition

open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem lifted_volume_le_cover_card
    {N D G : Type*} [MeasurableSpace N] [PseudoMetricSpace G]
    (μ : Measure N) (q : N → D → G) (A : Set D) (S : Set N)
    (t : Finset G) (ρ : ℝ) (V : ℝ≥0∞)
    (hball : ∀ y ∈ t, μ {u | ∃ d ∈ A, dist (q u d) y ≤ ρ} ≤ V)
    (hcover : ∀ u ∈ S, ∃ d ∈ A, ∃ y ∈ t, dist (q u d) y ≤ ρ) :
    μ S ≤ (t.card : ℝ≥0∞) * V := by
  classical
  calc
    μ S ≤ μ (⋃ y ∈ t, {u | ∃ d ∈ A, dist (q u d) y ≤ ρ}) := by
      apply measure_mono
      intro u hu
      obtain ⟨d, hd, y, hy, hdist⟩ := hcover u hu
      exact mem_iUnion₂.mpr ⟨y, hy, d, hd, hdist⟩
    _ ≤ ∑ y ∈ t, μ {u | ∃ d ∈ A, dist (q u d) y ≤ ρ} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ t, V := Finset.sum_le_sum hball
    _ = _ := by simp [nsmul_eq_mul]

theorem exponent_le_of_lifted_volume_covers
    {N D G : Type*} [MeasurableSpace N] [PseudoMetricSpace G]
    (μ : Measure N) (q : N → D → G) (A : ℕ → Set D) (S : ℕ → Set N)
    (t : ℕ → Finset G) (ρ : ℝ) (V : ℕ → ℝ) (hV0 : ∀ n, 0 ≤ V n)
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop) {p r : ℝ}
    (hV : HasSubexponentialUpperBoundSeq scale V)
    (hlower : HasSubexponentialLowerBoundSeq scale
      (fun n => (μ (S n)).toReal / Real.exp (scale n * p)))
    (hcount : HasSubexponentialUpperBoundSeq scale
      (fun n => ((t n).card : ℝ) / Real.exp (scale n * r)))
    (hball : ∀ n y, y ∈ t n → μ {u | ∃ d ∈ A n, dist (q u d) y ≤ ρ} ≤ ENNReal.ofReal (V n))
    (hcover : ∀ n u, u ∈ S n → ∃ d ∈ A n, ∃ y ∈ t n, dist (q u d) y ≤ ρ) :
    p ≤ r := by
  apply exponent_le_of_sequence_subexponential_bounds hs hlower
    (hcount.mul hV (Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _)
      (Real.exp_nonneg _))))
  apply Eventually.of_forall
  intro n
  have hb := lifted_volume_le_cover_card μ q (A n) (S n) (t n) ρ (ENNReal.ofReal (V n))
    (hball n) (hcover n)
  have hr := ENNReal.toReal_mono (show (t n).card * ENNReal.ofReal (V n) ≠ ⊤ from
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hb
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (hV0 n)] at hr
  rw [div_mul_cancel₀ _ (Real.exp_ne_zero _)]
  calc
    (μ (S n)).toReal ≤ ((t n).card : ℝ) * V n := hr
    _ = (((t n).card : ℝ) / Real.exp (scale n * r) * V n) * Real.exp (scale n * r) := by
      field_simp

end PolycyclicRecognition

end OAI
