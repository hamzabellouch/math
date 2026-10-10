import OAI.Analysis.KadisonKastler.MeasurablePoisson
import OAI.Analysis.KadisonKastler.PoissonBoundaryContinuity

namespace OAI

/-! # The actual demodulated smoothing fields

These are the fields used before polar decomposition. An essential bound
on the boundary, or an essential comparison with the modulated modular
unitaries, passes to a uniform norm bound at every positive height.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def demodulatedPoissonAverage (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (t r : ℝ) (hr : 0 < r) : H →L[ℂ] H :=
  ((Real.exp r : ℂ) * star (Circle.exp t : ℂ)) •
    measurablePoissonAverage F hF C hC t r hr

private theorem norm_demodulation_scalar (t r : ℝ) :
    ‖(Real.exp r : ℂ) * star (Circle.exp t : ℂ)‖ = Real.exp r := by
  rw [norm_mul, norm_star, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos r)]

omit [CompleteSpace H] in
theorem norm_demodulatedPoissonAverage_le
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (t r : ℝ) (hr : 0 < r) :
    ‖demodulatedPoissonAverage F hF C hC t r hr‖ ≤ Real.exp r * C := by
  rw [demodulatedPoissonAverage, norm_smul, norm_demodulation_scalar]
  exact mul_le_mul_of_nonneg_left (norm_measurablePoissonAverage_le F hF hC0 hC t r hr)
    (Real.exp_pos r).le

omit [CompleteSpace H] in
theorem continuous_demodulatedPoissonAverage
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (r : ℝ) (hr : 0 < r) :
    Continuous (fun t => demodulatedPoissonAverage F hF C hC t r hr) := by
  have hc : Continuous (fun t : ℝ => (Real.exp r : ℂ) * star (Circle.exp t : ℂ)) :=
    continuous_const.mul (continuous_subtype_val.comp Circle.exp.continuous).star
  exact hc.smul (continuous_measurablePoissonAverage F hF hC0 hC r hr)

/-- The comparison holds at every time, even when the boundary estimates
hold only almost everywhere. -/
theorem norm_demodulatedPoissonAverage_sub_boundary_le
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
    (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    {δ : ℝ} (hδ : 0 ≤ δ) (hFW : ∀ᵐ s, ‖F s - modulatedUnitaryField W s‖ ≤ δ)
    (t r : ℝ) (hr : 0 < r) :
    ‖demodulatedPoissonAverage F hF C hC t r hr - poissonBoundaryApprox W hW t r‖ ≤
      Real.exp r * δ := by
  have h := norm_measurablePoissonAverage_sub_le F (modulatedUnitaryField W) hF
    (fun x => (modulatedUnitaryField_continuous W hW x).aestronglyMeasurable)
    C 1 hC (ae_of_all _ (norm_modulatedUnitaryField_le_one W)) hδ hFW t r hr
  have he := measurablePoissonAverage_eq_poissonVectorAverage (modulatedUnitaryField W)
    (modulatedUnitaryField_continuous W hW) 1 (norm_modulatedUnitaryField_le_one W) t r hr
  unfold demodulatedPoissonAverage poissonBoundaryApprox
  rw [← he, ← smul_sub, norm_smul, norm_demodulation_scalar]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos r).le

end

end KadisonKastler

end OAI
