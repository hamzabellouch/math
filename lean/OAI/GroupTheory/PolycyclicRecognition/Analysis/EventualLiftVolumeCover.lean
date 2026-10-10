import OAI.GroupTheory.PolycyclicRecognition.Analysis.LiftVolumeCover

namespace OAI

/-! # Eventual volume comparison for lifted terminal sets -/

namespace PolycyclicRecognition

open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem exponent_le_of_lifted_volume_covers_eventually
    {N D G : Type*} [MeasurableSpace N] [PseudoMetricSpace G]
    (μ : Measure N) (q : N → D → G) (A : ℕ → Set D) (S : ℕ → Set N)
    (t : ℕ → Finset G) (ρ : ℝ) (V : ℕ → ℝ) (hV0 : ∀ n, 0 ≤ V n)
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop) {p r : ℝ}
    (hV : HasSubexponentialUpperBoundSeq scale V)
    (hlower : HasSubexponentialLowerBoundSeq scale
      (fun n => (μ (S n)).toReal / Real.exp (scale n * p)))
    (hcount : HasSubexponentialUpperBoundSeq scale
      (fun n => ((t n).card : ℝ) / Real.exp (scale n * r)))
    (hball : ∀ᶠ n in atTop, ∀ y ∈ t n,
      μ {u | ∃ d ∈ A n, dist (q u d) y ≤ ρ} ≤ ENNReal.ofReal (V n))
    (hcover : ∀ᶠ n in atTop, ∀ u ∈ S n,
      ∃ d ∈ A n, ∃ y ∈ t n, dist (q u d) y ≤ ρ) :
    p ≤ r := by
  apply exponent_le_of_sequence_subexponential_bounds hs hlower
    (hcount.mul hV (Eventually.of_forall (fun n =>
      div_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _))))
  filter_upwards [hball, hcover] with n hn hcovern
  have hb := lifted_volume_le_cover_card μ q (A n) (S n) (t n) ρ
    (ENNReal.ofReal (V n)) hn hcovern
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
