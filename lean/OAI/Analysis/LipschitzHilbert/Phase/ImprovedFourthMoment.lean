import OAI.Analysis.LipschitzHilbert.Phase.HomogeneousFourthMoment
import OAI.Analysis.LipschitzHilbert.Estimates.SequenceExponents
import OAI.Analysis.LipschitzHilbert.Estimates.SequenceNorms
import OAI.Analysis.LipschitzHilbert.Phase.DominantNormalization

namespace OAI

/-! The improved fourth moment: assembly of the quantitative gap and
the dominant-coefficient alternative from §7. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

def phaseParameter (D : ℝ) : ℝ := phaseConstant / Real.log (2 * D)

def fourthExponent (D : ℝ) : ℝ := 4 / (3 - phaseParameter D)

theorem nondominant_fourth_moment_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (hatom : ∀ i, coefficientMass a i ≤
      (1 - atomThreshold) * ∑ j, coefficientMass a j) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (∑ i, ‖a i‖ ^ fourthExponent D) ^ (3 - phaseParameter D) := by
  have hθ := phaseParameter_range hD
  have hmass := fourth_moment_quantile_gap_mass_cube_simplified ν frequency a
    hgap hsep hν atomThreshold_range.1 atomThreshold_range.2 hatom
  have hdim := fourth_power_exponent_comparison_exp a hD hcard phaseConstant_pos.le
    hθ.1.le hθ.2 rfl
  have hδ : 0 ≤ 1 - atomThreshold ^ 4 / 16384 := by norm_num [atomThreshold]
  have hR : 0 ≤ (∑ i, ‖a i‖ ^ fourthExponent D) ^ (3 - phaseParameter D) :=
    Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)) _
  calc
    _ ≤ (1 - atomThreshold ^ 4 / 16384) * (∑ i, coefficientMass a i) ^ 3 := hmass
    _ ≤ (1 - atomThreshold ^ 4 / 16384) *
        (Real.exp phaseConstant * (∑ i, ‖a i‖ ^ fourthExponent D) ^
          (3 - phaseParameter D)) := mul_le_mul_of_nonneg_left hdim hδ
    _ = ((1 - atomThreshold ^ 4 / 16384) * Real.exp phaseConstant) *
        (∑ i, ‖a i‖ ^ fourthExponent D) ^ (3 - phaseParameter D) := by ring
    _ ≤ 1 * (∑ i, ‖a i‖ ^ fourthExponent D) ^ (3 - phaseParameter D) :=
      mul_le_mul_of_nonneg_right (deficit_absorbs_exponential phaseConstant_le_gap) hR
    _ = _ := one_mul _

theorem mass_cube_le_two_sequenceNorm_fourth (a : ι → ℂ) {D : ℝ}
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) :
    (∑ i, coefficientMass a i) ^ 3 ≤ 2 * sequenceNorm a (fourthExponent D) ^ 4 := by
  have hθ := phaseParameter_range hD
  obtain ⟨_, _, heq⟩ := fourth_exponent_parameters hθ.1.le hθ.2
  have hinv : 4 / fourthExponent D = 3 - phaseParameter D := by
    dsimp [fourthExponent, phaseParameter]
    linarith [heq]
  have hdim := fourth_power_exponent_comparison_exp a hD hcard phaseConstant_pos.le
    hθ.1.le hθ.2 rfl
  rw [← Real.rpow_natCast (sequenceNorm a (fourthExponent D)) 4,
    sequenceNorm_rpow]
  norm_num only [Nat.cast_ofNat]
  rw [hinv]
  exact hdim.trans (mul_le_mul_of_nonneg_right phaseConstant_exp_le_two
    (Real.rpow_nonneg (Finset.sum_nonneg
      (fun i _ => Real.rpow_nonneg (norm_nonneg (a i)) _)) _))

theorem small_remainder_fourth_moment_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hzero : ∀ i, gap / 4 ≤ |frequency i|)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (hsmall : ∑ i, coefficientMass a i ≤ 1 / 1023) :
    (∫ t, ‖1 + finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (1 + ∑ i, ‖a i‖ ^ fourthExponent D) ^ (4 / fourthExponent D) := by
  have hθ := phaseParameter_range hD
  obtain ⟨hr, hrupper, _⟩ := fourth_exponent_parameters hθ.1.le hθ.2
  change 4 / 3 ≤ fourthExponent D at hr
  change fourthExponent D ≤ 3 / 2 at hrupper
  have hr0 : 0 < fourthExponent D := by linarith
  have hbpow : sequenceNorm a (fourthExponent D) ^ fourthExponent D =
      ∑ i, ‖a i‖ ^ fourthExponent D := by
    rw [sequenceNorm_rpow, div_self hr0.ne', Real.rpow_one]
  have h := finiteFourier_dominant_bound ν frequency a hgap hsep hν hzero
    (sequenceNorm_nonneg a _) (sequenceNorm_le_one_div_sixtyfour a hr hsmall)
    hr0 hrupper (sum_squares_le_sequenceNorm_sq a hr0 (by linarith))
    (mass_cube_le_two_sequenceNorm_fourth a hD hcard)
  change _ ≤ (1 + sequenceNorm a (fourthExponent D) ^ fourthExponent D) ^
    (4 / fourthExponent D) at h
  rwa [hbpow] at h

/-- The constant-one fourth-moment estimate with the improved coefficient
exponent, for arbitrary complex coefficients. This is the `p = 4` endpoint
of the manuscript's finite Fourier gain proposition. -/
theorem finite_fourth_moment_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (∑ i, ‖a i‖ ^ fourthExponent D) ^ (4 / fourthExponent D) := by
  classical
  by_cases ha : ∀ i, coefficientMass a i ≤
      (1 - atomThreshold) * ∑ j, coefficientMass a j
  · have h := nondominant_fourth_moment_bound ν frequency a hgap hsep hν hD hcard ha
    have hθ := phaseParameter_range hD
    have hp := (fourth_exponent_parameters hθ.1.le hθ.2).2.2
    have heq : 4 / fourthExponent D = 3 - phaseParameter D := by
      dsimp [fourthExponent, phaseParameter]
      linarith [hp]
    rwa [heq]
  · push Not at ha
    obtain ⟨i₀, hi₀⟩ := ha
    have h₀ := dominant_coefficient_ne_zero a i₀ hi₀
    have hcard' : (Fintype.card (RemainderIndex i₀) : ℝ) ≤ D := by
      exact (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hcard
    have hrest := small_remainder_fourth_moment_bound ν
      (remainderFrequency frequency i₀) (remainderCoefficient a i₀)
      hgap (remainderFrequency_separated hsep i₀) hν
      (remainderFrequency_away_zero hgap hsep i₀) hD hcard'
      (dominant_remainder_mass_le a i₀ hi₀)
    rw [remove_carrier_fourth_moment ν frequency a i₀ h₀]
    have hθ := phaseParameter_range hD
    have hr := (fourth_exponent_parameters hθ.1.le hθ.2).1
    have hr0 : 0 < fourthExponent D := by
      change 4 / 3 ≤ fourthExponent D at hr
      linarith
    exact (mul_le_mul_of_nonneg_left hrest (pow_nonneg (norm_nonneg _) _)).trans_eq
      (restore_coefficient_fourth_power a i₀ h₀ hr0)

theorem finite_fourier_l4_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ^ (1 / 4 : ℝ) ≤
      sequenceNorm a (fourthExponent D) := by
  have h := Real.rpow_le_rpow
    (integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _))
    (finite_fourth_moment_gain ν frequency a hgap hsep hν hD hcard)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [← Real.rpow_mul (Finset.sum_nonneg
    (fun i _ => Real.rpow_nonneg (norm_nonneg (a i)) _))] at h
  have heq : 4 / fourthExponent D * (1 / 4) = 1 / fourthExponent D := by ring
  simpa only [heq, sequenceNorm] using h

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
