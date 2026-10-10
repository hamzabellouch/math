import OAI.Analysis.LipschitzHilbert.Phase.HomogeneousFourthMoment
import OAI.Analysis.LipschitzHilbert.Estimates.SequenceExponents

namespace OAI

/-! Exact removal of a dominant Fourier carrier in §7. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

abbrev RemainderIndex (i₀ : ι) := {i : ι // i ≠ i₀}

def remainderFrequency (frequency : ι → ℝ) (i₀ : ι) (i : RemainderIndex i₀) : ℝ :=
  frequency i - frequency i₀

def remainderCoefficient (a : ι → ℂ) (i₀ : ι) (i : RemainderIndex i₀) : ℂ :=
  a i / a i₀

theorem remove_carrier_identity (frequency : ι → ℝ) (a : ι → ℂ)
    (i₀ : ι) (h₀ : a i₀ ≠ 0) (t : ℝ) :
    finiteFourierSum frequency a t = a i₀ * character (frequency i₀) t *
      (1 + finiteFourierSum (remainderFrequency frequency i₀) (remainderCoefficient a i₀) t) := by
  classical
  rw [finiteFourierSum, Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  rw [mul_add, mul_one, finiteFourierSum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [remainderFrequency, remainderCoefficient]
  calc
    a i * character (frequency i) t =
        (a i₀ * (a i / a i₀)) *
          (character (frequency i₀) t * character (frequency i - frequency i₀) t) := by
      rw [character_mul]
      have hf : frequency i₀ + (frequency i - frequency i₀) = frequency i := by ring
      rw [hf, mul_div_cancel₀ _ h₀]
    _ = _ := by ring

omit [Fintype ι] in
theorem remainderFrequency_separated {frequency : ι → ℝ} {gap : ℝ}
    (hsep : Separated frequency gap) (i₀ : ι) :
    Separated (remainderFrequency frequency i₀) gap := by
  intro i j hij
  have hval : (i : ι) ≠ j := fun h => hij (Subtype.ext h)
  have h := hsep hval
  simpa only [remainderFrequency, sub_sub_sub_cancel_right] using h

omit [Fintype ι] in
theorem remainderFrequency_away_zero {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (i₀ : ι)
    (i : RemainderIndex i₀) : gap / 4 ≤ |remainderFrequency frequency i₀ i| :=
  le_trans (by linarith) (hsep i.property)

omit [Fintype ι] in
theorem remainder_coefficientMass (a : ι → ℂ) (i₀ : ι) (i : RemainderIndex i₀) :
    coefficientMass (remainderCoefficient a i₀) i = coefficientMass a i / coefficientMass a i₀ := by
  unfold coefficientMass remainderCoefficient
  rw [norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _)]

theorem sum_remainder_coefficientMass (a : ι → ℂ) (i₀ : ι) :
    (∑ i : RemainderIndex i₀, coefficientMass (remainderCoefficient a i₀) i) =
      ((∑ i, coefficientMass a i) - coefficientMass a i₀) / coefficientMass a i₀ := by
  classical
  simp_rw [remainder_coefficientMass]
  rw [← Finset.sum_div]
  congr 1
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  ring

theorem sum_norm_remainder_rpow (a : ι → ℂ) (i₀ : ι) (r : ℝ) :
    (∑ i : RemainderIndex i₀, ‖remainderCoefficient a i₀ i‖ ^ r) =
      ((∑ i, ‖a i‖ ^ r) - ‖a i₀‖ ^ r) / ‖a i₀‖ ^ r := by
  classical
  simp_rw [remainderCoefficient, norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [← Finset.sum_div]
  congr 1
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  ring

theorem coefficient_norm_power_decomposition (a : ι → ℂ) (i₀ : ι)
    (h₀ : a i₀ ≠ 0) (r : ℝ) :
    (∑ i, ‖a i‖ ^ r) = ‖a i₀‖ ^ r *
      (1 + ∑ i : RemainderIndex i₀, ‖remainderCoefficient a i₀ i‖ ^ r) := by
  have hm : ‖a i₀‖ ^ r ≠ 0 := (Real.rpow_pos_of_pos (norm_pos_iff.mpr h₀) r).ne'
  rw [sum_norm_remainder_rpow]
  field_simp [hm]
  ring

theorem restore_coefficient_fourth_power (a : ι → ℂ) (i₀ : ι)
    (h₀ : a i₀ ≠ 0) {r : ℝ} (hr : 0 < r) :
    ‖a i₀‖ ^ 4 * (1 + ∑ i : RemainderIndex i₀, ‖remainderCoefficient a i₀ i‖ ^ r) ^ (4 / r) =
      (∑ i, ‖a i‖ ^ r) ^ (4 / r) := by
  rw [coefficient_norm_power_decomposition a i₀ h₀ r,
    Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _) (by positivity),
    ← Real.rpow_mul (norm_nonneg _)]
  have he : r * (4 / r) = 4 := by field_simp
  rw [he]
  norm_num

theorem dominant_coefficient_ne_zero (a : ι → ℂ) (i₀ : ι)
    (hdom : (1 - atomThreshold) * (∑ i, coefficientMass a i) < coefficientMass a i₀) :
    a i₀ ≠ 0 := by
  intro hz
  have hsum : 0 ≤ ∑ i, coefficientMass a i :=
    Finset.sum_nonneg fun i _ => coefficientMass_nonneg a i
  have hpos : 0 ≤ (1 - atomThreshold) * ∑ i, coefficientMass a i :=
    mul_nonneg (by norm_num [atomThreshold]) hsum
  simp [coefficientMass, hz] at hdom
  exact (not_lt_of_ge hpos) hdom

theorem dominant_remainder_mass_le (a : ι → ℂ) (i₀ : ι)
    (hdom : (1 - atomThreshold) * (∑ i, coefficientMass a i) < coefficientMass a i₀) :
    (∑ i : RemainderIndex i₀, coefficientMass (remainderCoefficient a i₀) i) ≤ 1 / 1023 := by
  have h₀ := dominant_coefficient_ne_zero a i₀ hdom
  have hm : 0 < coefficientMass a i₀ :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr h₀) _
  rw [sum_remainder_coefficientMass]
  apply (div_le_iff₀ hm).2
  norm_num [atomThreshold] at hdom
  linarith

theorem remove_carrier_norm (frequency : ι → ℝ) (a : ι → ℂ)
    (i₀ : ι) (h₀ : a i₀ ≠ 0) (t : ℝ) :
    ‖finiteFourierSum frequency a t‖ = ‖a i₀‖ *
      ‖1 + finiteFourierSum (remainderFrequency frequency i₀) (remainderCoefficient a i₀) t‖ := by
  rw [remove_carrier_identity frequency a i₀ h₀ t, norm_mul, norm_mul, norm_character, mul_one]

theorem remove_carrier_fourth_moment (ν : Measure ℝ)
    (frequency : ι → ℝ) (a : ι → ℂ) (i₀ : ι) (h₀ : a i₀ ≠ 0) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) =
      ‖a i₀‖ ^ 4 * ∫ t,
        ‖1 + finiteFourierSum (remainderFrequency frequency i₀) (remainderCoefficient a i₀) t‖ ^ 4 ∂ν := by
  simp_rw [remove_carrier_norm frequency a i₀ h₀, mul_pow]
  exact integral_const_mul _ _

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
