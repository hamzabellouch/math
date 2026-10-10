import OAI.Analysis.LipschitzHilbert.Estimates.WeakTwoIntegral
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

namespace OAI

/-! The exact weighted layer-cake step for a finite family of dilated
rectangles. Its measure is the sum of the top areas, not a counting measure. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert

theorem weighted_layer_from_weak_tail {ι : Type*} [Fintype ι] (w : ι → ℝ≥0) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (K : ℝ) (hK : 0 < K)
    (hS : 0 < ∑ i, (w i : ℝ))
    (htail : ∀ t : ℝ, 0 < t →
      (∑ i, if t < a i then (w i : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (K^2/t^2)) :
    (∑ i, (w i : ℝ≥0∞)*ENNReal.ofReal (a i)) ≤
      ENNReal.ofReal (2*K*Real.sqrt (∑ i, (w i : ℝ))) := by
  classical
  let : MeasurableSpace ι := ⊤
  let μ : Measure ι := ∑ i, w i • Measure.dirac i
  have hμset (s : Set ι) : μ s = ∑ i, if i ∈ s then (w i : ℝ≥0∞) else 0 := by
    simp only [μ, Measure.finsetSum_apply, Measure.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ s <;> simp [hi, ENNReal.smul_def]
  have hμuniv : μ univ = ∑ i, (w i : ℝ≥0∞) := by simp [hμset]
  have hmass : (μ univ).toReal = ∑ i, (w i : ℝ) := by
    rw [hμuniv, ENNReal.toReal_sum]
    · simp
    · intro i _; exact ENNReal.coe_ne_top
  have : IsFiniteMeasure μ := by
    constructor
    rw [hμuniv]
    exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.coe_lt_top)
  have hnonzero : μ univ ≠ 0 := by
    intro h
    rw [h, ENNReal.toReal_zero] at hmass
    linarith
  have h := weak_two_lintegral μ hnonzero a (measurable_of_countable a).aemeasurable
    (Filter.Eventually.of_forall ha) K hK (by
      intro t ht
      simpa only [hμset, mem_ofPred_eq] using htail t ht)
  rw [hmass] at h
  convert h using 1
  change (∑ i, (w i : ℝ≥0∞)*ENNReal.ofReal (a i)) =
    ∫⁻ x, ENNReal.ofReal (a x) ∂(∑ i, w i • Measure.dirac i)
  rw [lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_smul_measure, lintegral_dirac]
  simp only [ENNReal.smul_def, smul_eq_mul]

end LipschitzHilbert

end

end OAI
