import OAI.Analysis.KadisonKastler.CauchyCharacter
import OAI.Analysis.KadisonKastler.MeasurablePoisson

namespace OAI

/-! # Actual Poisson averages of scalar characters -/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

theorem integral_realPoissonKernel_character (t s : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ, (realPoissonKernel t r x : ℂ) * (Circle.exp (s * x) : ℂ)) =
      (Real.exp (-r * |s|) : ℂ) * (Circle.exp (s * t) : ℂ) := by
  have hγ : (0 : NNReal) < NNReal.mk r hr.le := hr
  simpa only [← realPoissonKernel_eq_cauchyPDFReal t _ hr.le, NNReal.coe_mk] using
    integral_cauchyPDFReal_character hγ t s

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scalar characters, regarded as a concrete field of operators. -/
def poissonCharacterField (s t : ℝ) : H →L[ℂ] H := (Circle.exp (s * t) : ℂ) • 1

omit [CompleteSpace H] in
theorem poissonCharacterField_measurable (s : ℝ) (x : H) :
    AEStronglyMeasurable (fun t => poissonCharacterField s t x) volume := by
  change AEStronglyMeasurable (fun t => (Circle.exp (s * t) : ℂ) • x) volume
  exact (((continuous_subtype_val.comp Circle.exp.continuous).comp
    (continuous_const.mul continuous_id)).smul continuous_const).aestronglyMeasurable

omit [CompleteSpace H] in
theorem norm_poissonCharacterField_le (s t : ℝ) : ‖poissonCharacterField (H := H) s t‖ ≤ 1 := by
  rw [poissonCharacterField, norm_smul, Circle.norm_coe, one_mul]
  exact ContinuousLinearMap.norm_id_le

/-- The explicit Cauchy character formula for the vector-defined Poisson
average, with the same field and integral used by analytic smoothing. -/
theorem measurablePoissonAverage_character (s t : ℝ) {r : ℝ} (hr : 0 < r) :
    measurablePoissonAverage (poissonCharacterField (H := H) s)
      (poissonCharacterField_measurable s) 1
      (Filter.Eventually.of_forall (norm_poissonCharacterField_le s)) t r hr =
      ((Real.exp (-r * |s|) : ℂ) * (Circle.exp (s * t) : ℂ)) •
        (1 : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [measurablePoissonAverage_apply]
  change (∫ u : ℝ, realPoissonKernel t r u • ((Circle.exp (s * u) : ℂ) • x)) = _
  have he (u : ℝ) : realPoissonKernel t r u • ((Circle.exp (s * u) : ℂ) • x) =
      ((realPoissonKernel t r u : ℂ) * (Circle.exp (s * u) : ℂ)) • x := by
    exact (smul_assoc (realPoissonKernel t r u) (Circle.exp (s * u) : ℂ) x).symm.trans
      (congrArg (fun z : ℂ => z • x)
        (RCLike.real_smul_eq_coe_mul (realPoissonKernel t r u) (Circle.exp (s * u) : ℂ)))
  simp_rw [he]
  rw [integral_smul_const, integral_realPoissonKernel_character t s hr]
  rfl

end

end KadisonKastler

end OAI
