import OAI.Analysis.KadisonKastler.PoissonCharacter
import OAI.Analysis.KadisonKastler.PoissonProductEstimates

namespace OAI

/-! # Exact cancellation of the Poisson modulation

The modulation of a unitary field and its inverse has scalar frequency two.
The Cauchy character formula therefore cancels the two demodulating factors
exactly. This is proved for the actual vector-defined averages.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem demodulation_scalar_cancel (t r : ℝ) :
    (((Real.exp r : ℂ) * star (Circle.exp t : ℂ)) ^ 2) *
      ((Real.exp (-2 * r) : ℂ) * (Circle.exp (2 * t) : ℂ)) = 1 := by
  have hc : star (Circle.exp t : ℂ) * (Circle.exp t : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_mul']
    simp only [Circle.norm_coe, one_pow, Complex.ofReal_one]
  have he : (Real.exp r : ℂ) ^ 2 * (Real.exp (-2 * r) : ℂ) = 1 := by
    rw [pow_two, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Real.exp_add, ← Real.exp_add]
    rw [show r + r + -2 * r = 0 by ring, Real.exp_zero, Complex.ofReal_one]
  have hd : (Circle.exp (2 * t) : ℂ) = (Circle.exp t : ℂ) ^ 2 := by
    rw [two_mul, Circle.exp_add, Circle.coe_mul, pow_two]
  rw [hd]
  calc
    _ = ((Real.exp r : ℂ) ^ 2 * (Real.exp (-2 * r) : ℂ)) *
        (star (Circle.exp t : ℂ) * (Circle.exp t : ℂ)) ^ 2 := by ring
    _ = 1 := by rw [hc, he]; norm_num

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem measurablePoissonAverage_congr_ae
    (F G : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (hG : ∀ x, AEStronglyMeasurable (fun s => G s x) volume)
    (C D : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (hD : ∀ᵐ s, ‖G s‖ ≤ D)
    (hFG : ∀ᵐ s, F s = G s) (t r : ℝ) (hr : 0 < r) :
    measurablePoissonAverage F hF C hC t r hr =
      measurablePoissonAverage G hG D hD t r hr := by
  apply ContinuousLinearMap.ext
  intro x
  rw [measurablePoissonAverage_apply, measurablePoissonAverage_apply]
  apply integral_congr_ae
  filter_upwards [hFG] with s hs
  rw [hs]

/-- Cancellation for any bounded measurable field agreeing with the
frequency-two character almost everywhere. -/
theorem measurablePoissonAverage_phase_cancel
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
    (hFchar : ∀ᵐ s, F s = poissonCharacterField 2 s)
    (t r : ℝ) (hr : 0 < r) :
    (((Real.exp r : ℂ) * star (Circle.exp t : ℂ)) ^ 2) •
      measurablePoissonAverage F hF C hC t r hr = 1 := by
  rw [measurablePoissonAverage_congr_ae F (poissonCharacterField 2) hF
    (poissonCharacterField_measurable 2) C 1 hC
    (Filter.Eventually.of_forall (norm_poissonCharacterField_le 2)) hFchar t r hr,
    measurablePoissonAverage_character, smul_smul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [show -r * 2 = -2 * r by ring, demodulation_scalar_cancel, one_smul]

/-- The pointwise identity behind inverse comparison, for an arbitrary
unitary field without continuity assumptions. -/
theorem modulatedUnitaryField_mul_inverse (W : ℝ → unitary (H →L[ℂ] H)) (s : ℝ) :
    modulatedUnitaryField W s * modulatedUnitaryField (fun t => star (W t)) s =
      poissonCharacterField 2 s := by
  simp only [modulatedUnitaryField, poissonCharacterField,
    smul_mul_assoc, mul_smul_comm, smul_smul, Unitary.coe_star,
    Unitary.mul_star_self_of_mem (W s).property]
  rw [two_mul, Circle.exp_add, Circle.coe_mul]

end

end KadisonKastler

end OAI
