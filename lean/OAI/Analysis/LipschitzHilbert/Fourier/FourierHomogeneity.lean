import OAI.Analysis.LipschitzHilbert.Estimates.SequenceNorms

namespace OAI

/-! Restoring arbitrary coefficients after a unit sequence-norm estimate. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

def normalizedCoefficient (a : ι → ℂ) (r : ℝ) (i : ι) : ℂ :=
  a i / (sequenceNorm a r : ℂ)

theorem sequenceNorm_pos_of_nonzero (a : ι → ℂ) (r : ℝ)
    (ha : ∃ i, a i ≠ 0) : 0 < sequenceNorm a r := by
  obtain ⟨i, hi⟩ := ha
  have hsum : 0 < ∑ i, ‖a i‖ ^ r :=
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr hi) r).trans_le
      (Finset.single_le_sum (fun j _ => Real.rpow_nonneg (norm_nonneg (a j)) r)
        (Finset.mem_univ i))
  exact Real.rpow_pos_of_pos hsum (1 / r)

theorem normalizedCoefficient_unit (a : ι → ℂ) {r : ℝ} (hr : 0 < r)
    (ha : ∃ i, a i ≠ 0) :
    ∑ i, ‖normalizedCoefficient a r i‖ ^ r = 1 := by
  have hn := sequenceNorm_pos_of_nonzero a r ha
  have hp : sequenceNorm a r ^ r = ∑ i, ‖a i‖ ^ r := by
    rw [sequenceNorm_rpow, div_self hr.ne', Real.rpow_one]
  have hnorm : ‖(sequenceNorm a r : ℂ)‖ = sequenceNorm a r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  simp_rw [normalizedCoefficient, norm_div, hnorm,
    Real.div_rpow (norm_nonneg _) hn.le]
  rw [← Finset.sum_div, ← hp, div_self (Real.rpow_pos_of_pos hn r).ne']

theorem finiteFourierSum_normalized (frequency : ι → ℝ) (a : ι → ℂ) (r t : ℝ) :
    finiteFourierSum frequency (normalizedCoefficient a r) t =
      finiteFourierSum frequency a t / (sequenceNorm a r : ℂ) := by
  unfold finiteFourierSum normalizedCoefficient
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem restore_normalized_fourier_norm (frequency : ι → ℝ) (a : ι → ℂ)
    (r : ℝ) (ha : ∃ i, a i ≠ 0) (t : ℝ) :
    ‖finiteFourierSum frequency a t‖ = sequenceNorm a r *
      ‖finiteFourierSum frequency (normalizedCoefficient a r) t‖ := by
  have hn := sequenceNorm_pos_of_nonzero a r ha
  rw [finiteFourierSum_normalized, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hn]
  field_simp

theorem homogeneous_fourier_power_bound (ν : Measure ℝ) (frequency : ι → ℝ)
    {r p : ℝ} (hr : 0 < r) (hp : 0 < p)
    (hunit : ∀ a : ι → ℂ, (∑ i, ‖a i‖ ^ r) = 1 →
      (∫ t, ‖finiteFourierSum frequency a t‖ ^ p ∂ν) ≤ 1) (a : ι → ℂ) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ p ∂ν) ≤ sequenceNorm a r ^ p := by
  classical
  by_cases ha : ∃ i, a i ≠ 0
  · have hn := sequenceNorm_pos_of_nonzero a r ha
    have h := hunit (normalizedCoefficient a r) (normalizedCoefficient_unit a hr ha)
    have heq : (fun t => ‖finiteFourierSum frequency a t‖ ^ p) =
        (fun t => sequenceNorm a r ^ p *
          ‖finiteFourierSum frequency (normalizedCoefficient a r) t‖ ^ p) := by
      funext t
      rw [restore_normalized_fourier_norm frequency a r ha t,
        Real.mul_rpow hn.le (norm_nonneg _)]
    rw [heq, integral_const_mul]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hn.le p) h
  · have hz : a = 0 := by
      funext i
      exact not_ne_iff.mp (fun hi => ha ⟨i, hi⟩)
    subst a
    simp [finiteFourierSum, sequenceNorm, Real.zero_rpow hp.ne', Real.zero_rpow hr.ne',
      Real.zero_rpow (inv_ne_zero hr.ne')]

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
