import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitGeometry
import OAI.Analysis.IrrationalRotation.Product.OneCoordinateDensity
import OAI.Analysis.IrrationalRotation.Analysis.FiniteKernelMixture

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

lemma baseLaw_bin {r : ℕ} [NeZero r] (d : Fin r) :
    baseLaw (bin r d) = (r : ℝ≥0∞)⁻¹ := by
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  rw [baseLaw_eq_restrict, Measure.restrict_apply (show MeasurableSet (bin r d) from measurableSet_Ico),
    inter_eq_left.mpr (bin_subset_unit d)]
  rw [bin, Real.volume_Ico, bin_length]
  rw [ENNReal.ofReal_div_of_pos hr]
  simp

lemma labelsGivenDigit_singleton (side : Bool) (r : ℕ) (κ m a b t : ℝ)
    (d : Fin r) (l : Label) :
    labelsGivenDigit side r κ m a b t d {l} =
      digitWeight side r κ m a b t l d / ∑ k, digitWeight side r κ m a b t k d := by
  classical
  cases l <;> simp [labelsGivenDigit, FiniteKernelMixture.normalizedKernel_apply,
    Kernel.const_apply, Pi.single_apply]

variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)

include hm ha ha' hb hb' in
lemma endpointLaw_isProbabilityMeasure (side : Bool) (l : Label) :
    IsProbabilityMeasure (endpointLaw side m a b l) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  cases l with
  | none => exact baseLaw_isProbabilityMeasure
  | some i =>
    cases side
    · exact leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb' i
    · exact rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb' i

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma labelMass_sum : (∑ l, labelMass κ m a b t l) = 1 := by
  have hm0 : 0 < m := by linarith
  have hq0 : 0 ≤ diagonalMass κ m a b t :=
    le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  have hp0 := componentProbabilities_nonneg (a := a) (b := b) hκ0 hm0 ht0
  rw [Fintype.sum_option]
  change ENNReal.ofReal (diagonalMass κ m a b t) +
    ∑ i, ENNReal.ofReal (componentProbabilities κ m a b t i) = 1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp0 i),
    ← ENNReal.ofReal_add hq0 (Finset.sum_nonneg (fun i _ => hp0 i))]
  have heq : diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i = 1 := by
    simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    unfold diagonalMass
    ring
  rw [heq]
  norm_num

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma rawLaw_isProbabilityMeasure : IsProbabilityMeasure (rawLaw κ m a b t) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  apply labelledMixture_isProbabilityMeasure
  have h := labelMass_sum hκ0 hκ hm ha ha' hb hb' ht0 ht
  simpa only [Fintype.sum_option, labelMass] using h

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma digitWeight_total_ne_zero (side : Bool) (r : ℕ) [NeZero r] (d : Fin r) :
    (∑ l, digitWeight side r κ m a b t l d) ≠ 0 := by
  have hq : 0 < diagonalMass κ m a b t := by
    have := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    linarith
  have hpos : digitWeight side r κ m a b t none d ≠ 0 := by
    simp only [digitWeight, labelMass, endpointLaw, baseLaw_bin]
    exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hq)
      (ENNReal.inv_ne_zero.mpr (by simp))
  intro h
  apply hpos
  exact (Finset.sum_eq_zero_iff.mp h) none (Finset.mem_univ none)

include hm ha ha' hb hb' in
lemma digitWeight_total_ne_top (side : Bool) (r : ℕ) (d : Fin r) :
    (∑ l, digitWeight side r κ m a b t l d) ≠ ∞ := by
  have : ∀ l, IsProbabilityMeasure (endpointLaw side m a b l) :=
    endpointLaw_isProbabilityMeasure hm ha ha' hb hb' side
  apply ENNReal.sum_ne_top.mpr
  intro l _
  apply ENNReal.mul_ne_top
  · cases l <;> exact ENNReal.ofReal_ne_top
  · exact measure_ne_top _ _

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma labelsGivenDigit_isMarkov (side : Bool) (r : ℕ) [NeZero r] :
    IsMarkovKernel (labelsGivenDigit side r κ m a b t) := by
  apply FiniteKernelMixture.normalizedKernel_isMarkov
  · exact digitWeight_total_ne_zero hκ0 hκ hm ha ha' hb hb' ht0 ht side r
  · exact digitWeight_total_ne_top hm ha ha' hb hb' side r

end Invariant233.CircleDigitCoupling

end

end OAI
