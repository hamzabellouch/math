import OAI.Analysis.LpDimension.StableIntensity

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace
universe u uE uF

namespace SubpolynomialLp

section Compound
variable {E : Type uE} [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]

def convolutionPower (μ : Measure E) : ℕ → Measure E
  | 0 => Measure.dirac 0
  | n+1 => convolutionPower μ n ∗ μ

instance convolutionPower_probability (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (convolutionPower μ n) := by
  induction n with
  | zero => dsimp [convolutionPower]; infer_instance
  | succ n ih => dsimp [convolutionPower]; infer_instance

def compoundPoisson (r : ℝ≥0) (μ : Measure E) : Measure E :=
  Measure.sum (fun n => ENNReal.ofReal (Real.exp (-r)*r^n/(n.factorial)) • convolutionPower μ n)

instance compoundPoisson_probability (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (compoundPoisson r μ) := by
  constructor
  simp only [compoundPoisson, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (hasSum_one_poissonMeasure r).summable, (hasSum_one_poissonMeasure r).tsum_eq]
  simp

omit [MeasurableAdd₂ E] in
omit [MeasurableAdd₂ E] in
lemma integral_compoundPoisson {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℝ≥0) (μ : Measure E) (f : E → F) (hf : Integrable f (compoundPoisson r μ)) :
    (∫ x, f x ∂compoundPoisson r μ) =
      ∑' n, (Real.exp (-r)*r^n/(n.factorial):ℝ) • ∫ x, f x ∂convolutionPower μ n := by
  rw [compoundPoisson, integral_sum_measure hf]
  congr with n
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

lemma convolutionPower_map {F : Type uF} [AddCommMonoid F] [MeasurableSpace F] [MeasurableAdd₂ F]
    (μ : Measure E) [IsProbabilityMeasure μ] (L : E →+ F) (hL : Measurable L) (n : ℕ) :
    (convolutionPower μ n).map L = convolutionPower (μ.map L) n := by
  have : IsProbabilityMeasure (μ.map L) := inferInstance
  induction n with
  | zero => simp [convolutionPower, Measure.map_dirac' hL 0]
  | succ n ih => rw [convolutionPower, Measure.map_conv_addMonoidHom L hL, ih, convolutionPower]


end Compound

section Characteristic
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma charFun_convolutionPower (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (t : E) :
    charFun (convolutionPower μ n) t = (charFun μ t)^n := by
  induction n with
  | zero => simp [convolutionPower, charFun_dirac]
  | succ n ih => rw [convolutionPower, charFun_conv, ih, pow_succ]

lemma charFun_compoundPoisson (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ] (t : E) :
    charFun (compoundPoisson r μ) t = Complex.exp (r * (charFun μ t-1)) := by
  rw [charFun_apply, integral_compoundPoisson]
  · simp only [← charFun_apply, charFun_convolutionPower, Complex.real_smul]
    calc
      (∑' n, (Real.exp (-r)*r^n/(n.factorial):ℝ)*(charFun μ t)^n) =
          (Real.exp (-r):ℂ) * ∑' n, ((r:ℂ)*charFun μ t)^n/(n.factorial) := by
        rw [← tsum_mul_left]
        congr with n
        push_cast
        ring
      _ = (Real.exp (-r):ℂ)*Complex.exp ((r:ℂ)*charFun μ t) := by
        rw [(NormedSpace.expSeries_div_hasSum_exp ((r:ℂ)*charFun μ t)).tsum_eq, Complex.exp_eq_exp_ℂ]
      _ = _ := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        push_cast
        ring
  · exact (integrable_const (1:ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])

end Characteristic

lemma exp_integrable_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) (hμ : Integrable (fun x => Real.exp (t*x)) μ)
    (hν : Integrable (fun x => Real.exp (t*x)) ν) :
    Integrable (fun x => Real.exp (t*x)) (μ ∗ ν) := by
  rw [integrable_conv_iff (by fun_prop)]
  constructor
  · exact ae_of_all _ fun x => by
      simpa only [mul_add, Real.exp_add] using hν.const_mul (Real.exp (t*x))
  · simp only [Real.norm_eq_abs]
    simp_rw [abs_of_pos (Real.exp_pos _), mul_add, Real.exp_add, integral_const_mul]
    exact hμ.mul_const _

lemma exp_integral_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) (hμ : Integrable (fun x => Real.exp (t*x)) μ)
    (hν : Integrable (fun x => Real.exp (t*x)) ν) :
    (∫ x, Real.exp (t*x) ∂(μ ∗ ν)) =
      (∫ x, Real.exp (t*x) ∂μ) * ∫ x, Real.exp (t*x) ∂ν := by
  rw [integral_conv (exp_integrable_conv μ ν t hμ hν)]
  simp only [mul_add, Real.exp_add, integral_const_mul, integral_mul_const]

lemma exp_convolutionPower (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ)
    (hμ : Integrable (fun x => Real.exp (t*x)) μ) (n : ℕ) :
    Integrable (fun x => Real.exp (t*x)) (convolutionPower μ n) ∧
    (∫ x, Real.exp (t*x) ∂convolutionPower μ n) = (∫ x, Real.exp (t*x) ∂μ)^n := by
  induction n with
  | zero => exact ⟨integrable_dirac (by simp), by simp [convolutionPower]⟩
  | succ n ih =>
    exact ⟨exp_integrable_conv _ _ t ih.1 hμ, by
      rw [convolutionPower, exp_integral_conv _ _ t ih.1 hμ, ih.2, pow_succ]⟩


lemma bounded_exp_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (B : ℝ)
    (hB : ∀ᵐ x ∂μ, |x| ≤ B) (t : ℝ) : Integrable (fun x => Real.exp (t*x)) μ := by
  apply (integrable_const (Real.exp (|t| * B))).mono' (by fun_prop)
  filter_upwards [hB] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc t*x ≤ |t*x| := le_abs_self _
       _ = |t| * |x| := abs_mul _ _
       _ ≤ |t| * B := mul_le_mul_of_nonneg_left hx (abs_nonneg _)


def symmetrize (μ : Measure ℝ) : Measure ℝ :=
  (2:ℝ≥0∞)⁻¹ • μ + (2:ℝ≥0∞)⁻¹ • μ.map Neg.neg

instance symmetrize_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (symmetrize μ) := by
  have : IsProbabilityMeasure (μ.map Neg.neg) := inferInstance
  constructor
  simp [symmetrize, Measure.add_apply, Measure.smul_apply]
  exact ENNReal.inv_two_add_inv_two

lemma integral_symmetrize {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure ℝ) (f : ℝ → F) (hf : Integrable f μ)
    (hn : Integrable (fun x => f (-x)) μ) :
    (∫ x, f x ∂symmetrize μ) = (1/2:ℝ) • ((∫ x, f x ∂μ)+(∫ x, f (-x) ∂μ)) := by
  have hmap : Integrable f (μ.map Neg.neg) :=
    (measurableEmbedding_neg.integrable_map_iff).mpr hn
  rw [symmetrize, integral_add_measure (hf.smul_measure (by norm_num))
    (hmap.smul_measure (by norm_num)), integral_smul_measure, integral_smul_measure,
    integral_map (by fun_prop) hmap.aestronglyMeasurable]
  norm_num [ENNReal.toReal_inv, div_eq_inv_mul, smul_add]

lemma charFun_symmetrize (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    charFun (symmetrize μ) t = (∫ x, Real.cos (t*x) ∂μ : ℝ) := by
  rw [charFun_apply_real, integral_symmetrize]
  · rw [← integral_add]
    · rw [← integral_smul, ← integral_complex_ofReal]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        simp only [Complex.real_smul]
        simp only [Complex.ofReal_neg, mul_neg]
        rw [Complex.exp_mul_I, Complex.exp_mul_I]
        simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_mul,
          ← Complex.ofReal_cos]
        push_cast
        ring
    · exact (integrable_const (1:ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])
    · exact (integrable_const (1:ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])
  · exact (integrable_const (1:ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])
  · exact (integrable_const (1:ℝ)).mono (by fun_prop) (by simp [Complex.norm_exp])

end SubpolynomialLp

end

end OAI
