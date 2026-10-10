import OAI.Analysis.LipschitzHilbert.Estimates.BoxVariationWeights
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! Sum the decaying top-box exceptional areas over the entire plane.
This uses the actual summable lattice weight, rather than discarding
the boxes outside the top rectangle. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace LipschitzHilbert

theorem boxVariationWeight_tsum :
    (∑' p : ℤ × ℤ, ENNReal.ofReal (boxVariationWeight p)) ≤
      ENNReal.ofReal ((4*Real.pi)^2) := by
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => (boxVariationWeight_pos p).le)]
  apply ENNReal.ofReal_le_ofReal
  have h := boxVariationWeight_sum (fun p : s => (p : ℤ × ℤ)) Subtype.val_injective
  simpa only [Finset.univ_eq_attach, Finset.sum_attach] using h

theorem global_exceptional_area {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (bad : ℤ × ℤ → Set Ω) (A : ℝ≥0∞)
    (hbad : ∀ p, μ (bad p) ≤ A * ENNReal.ofReal (boxVariationWeight p)) :
    μ (⋃ p, bad p) ≤ A * ENNReal.ofReal ((4*Real.pi)^2) := by
  calc
    _ ≤ ∑' p, μ (bad p) := measure_iUnion_le _
    _ ≤ ∑' p, A * ENNReal.ofReal (boxVariationWeight p) := ENNReal.tsum_le_tsum hbad
    _ = A * ∑' p, ENNReal.ofReal (boxVariationWeight p) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl boxVariationWeight_tsum

end LipschitzHilbert

end

end OAI
