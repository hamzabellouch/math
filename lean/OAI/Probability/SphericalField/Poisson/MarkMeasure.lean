import Mathlib
import OAI.Probability.SphericalField.Poisson.PositiveMass

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
def poissonMarkMeasure {S : Type*} [MeasurableSpace S] (η : Measure (ℝ × S)) : Measure S :=
  (η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1))).map Prod.snd

lemma poissonMarkMeasure_measurable {S : Type*} [MeasurableSpace S] :
    Measurable (poissonMarkMeasure (S := S)) :=
  (Measure.measurable_map _ measurable_snd).comp
    (measurable_measure_withDensity_fixed (by fun_prop))

lemma normalizedMeasure_probability {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (h0 : μ univ ≠ 0) (hf : μ univ ≠ ⊤) : IsProbabilityMeasure (normalizedMeasure μ) := by
  constructor
  change (μ univ)⁻¹ * μ univ = 1
  exact ENNReal.inv_mul_cancel h0 hf

lemma normalizedMeasure_smul {S : Type*} [MeasurableSpace S] (μ : Measure S)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcf : c ≠ ⊤) :
    normalizedMeasure (c • μ) = normalizedMeasure μ := by
  unfold normalizedMeasure
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.mul_inv (Or.inl hc0) (Or.inl hcf),smul_smul]
  congr 1
  calc
    c⁻¹ * (μ univ)⁻¹ * c = c⁻¹*c*(μ univ)⁻¹ := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hc0 hcf,one_mul]

lemma map_withDensity_comp {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) {f : S → T} (hf : Measurable f) {g : T → ℝ≥0∞} (hg : Measurable g) :
    (μ.map f).withDensity g = (μ.withDensity (g ∘ f)).map f := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_withDensity_eq_lintegral_mul _ hg hh,
    lintegral_map (hg.mul hh) hf,lintegral_map hh hf]
  rw [lintegral_withDensity_eq_lintegral_mul _ (hg.comp hf) (show Measurable (fun x => h (f x)) from hh.comp hf)]
  rfl

lemma poissonMarkMeasure_shift {S : Type*} [MeasurableSpace S]
    (η : Measure (ℝ × S)) {F : S → ℝ} (hF : Measurable F) :
    poissonMarkMeasure (η.map (logMarkShift F)) =
      (poissonMarkMeasure η).withDensity (fun s => ENNReal.ofReal (Real.exp (F s))) := by
  unfold poissonMarkMeasure
  rw [map_withDensity_comp _ (logMarkShift_measurable hF) (by fun_prop),
    Measure.map_map measurable_snd (logMarkShift_measurable hF),
    map_withDensity_comp _ measurable_snd (by fun_prop),← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  congr 1
  funext p
  simp only [Function.comp_def,logMarkShift,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le,Pi.mul_apply]

lemma poissonMarkMeasure_mass {S : Type*} [MeasurableSpace S] (η : Measure (ℝ × S)) :
    poissonMarkMeasure η univ = ∫⁻ p, ENNReal.ofReal (Real.exp p.1) ∂η := by
  unfold poissonMarkMeasure
  rw [Measure.map_apply measurable_snd MeasurableSet.univ]
  simp only [preimage_univ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]

lemma poissonMarkMeasure_probability {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν),
      IsProbabilityMeasure (normalizedMeasure (poissonMarkMeasure η)) := by
  have he : (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map (Measure.map Prod.fst) =
      poissonRandomMeasureLaw (stableLogIntensity b) := by
    rw [poissonRandomMeasureLaw_map _ measurable_fst]
    simp only [Measure.map_fst_prod,measure_univ,one_smul]
  have hh : ∀ᵐ η ∂poissonRandomMeasureLaw (stableLogIntensity b),
      (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η) ≠ 0 ∧
      (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η) ≠ ⊤ := by
    filter_upwards [stablePoisson_total_positive hb0,stablePoisson_total_finite hb0 hb1] with η h1 h2
    exact ⟨h1.ne',h2⟩
  rw [← he] at hh
  have hmeas : Measurable (fun η : Measure ℝ => ∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η) :=
    Measure.measurable_lintegral (by fun_prop)
  have hh' := (ae_map_iff (Measure.measurable_map _ measurable_fst).aemeasurable
    (((measurableSet_eq_fun hmeas measurable_const).compl).inter
      ((measurableSet_eq_fun hmeas measurable_const).compl))).mp hh
  filter_upwards [hh'] with η hη
  change (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η.map Prod.fst) ≠ 0 ∧
    (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η.map Prod.fst) ≠ ⊤ at hη
  rw [lintegral_map (by fun_prop) measurable_fst] at hη
  exact normalizedMeasure_probability _ (by simpa only [poissonMarkMeasure_mass] using hη.1) (by simpa only [poissonMarkMeasure_mass] using hη.2)

lemma stablePoisson_gibbs_measure_law {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 ≤ b)
    {F : S → ℝ} (hF : Measurable F) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map
      (fun η => normalizedMeasure ((poissonMarkMeasure η).withDensity
        (fun s => ENNReal.ofReal (Real.exp (F s))))) =
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod
      (ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b*F s)))))).map
        (fun η => normalizedMeasure (poissonMarkMeasure η)) := by
  rw [← stablePoisson_mark_shift ν hb hF,
    Measure.map_map (show Measurable (fun η => normalizedMeasure (poissonMarkMeasure η)) from
      normalizedMeasure_measurable.comp poissonMarkMeasure_measurable)
      (show Measurable (Measure.map (logMarkShift F)) from
        Measure.measurable_map _ (logMarkShift_measurable hF))]
  congr 1
  funext η
  simp only [Function.comp_def,poissonMarkMeasure_shift η hF]

open Matrix
open scoped RealInnerProductSpace MatrixOrder

abbrev CovarianceMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] := {C : Matrix ι ι ℝ // C.PosSemidef}

instance covarianceMatrixMeasurableSpace (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MeasurableSpace (CovarianceMatrix ι) :=
  inferInstanceAs (MeasurableSpace {C : ι → ι → ℝ // Matrix.PosSemidef C})

instance covarianceMatrixBorelSpace (ι : Type*) [Fintype ι] [DecidableEq ι] :
    BorelSpace (CovarianceMatrix ι) :=
  inferInstanceAs (BorelSpace {C : ι → ι → ℝ // Matrix.PosSemidef C})

def gaussianCovarianceLaw {ι : Type*} [Fintype ι] [DecidableEq ι] (p : EuclideanSpace ℝ ι × CovarianceMatrix ι) :
    ProbabilityMeasure (EuclideanSpace ℝ ι) := ⟨multivariateGaussian p.1 p.2.val, inferInstance⟩

lemma gaussianCovarianceLaw_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (gaussianCovarianceLaw (ι := ι)) := by
  classical
  have : SequentialSpace (EuclideanSpace ℝ ι × CovarianceMatrix ι) :=
    inferInstanceAs (SequentialSpace (EuclideanSpace ℝ ι × {C : ι → ι → ℝ // Matrix.PosSemidef C}))
  rw [continuous_iff_seqContinuous]
  intro p p₀ hp
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  change Tendsto (fun n => charFun (multivariateGaussian (p n).1 (p n).2.val) t) atTop
    (𝓝 (charFun (multivariateGaussian p₀.1 p₀.2.val) t))
  simp_rw [charFun_multivariateGaussian (p _).2.property,charFun_multivariateGaussian p₀.2.property]
  have hc : Continuous (fun q : EuclideanSpace ℝ ι × CovarianceMatrix ι =>
      Complex.exp (((inner ℝ t q.1 : ℝ) : ℂ)*Complex.I -
        ((∑ i, t i * ∑ j, q.2.val i j * t j : ℝ) : ℂ)/2)) := by
    have he (i j : ι) : Continuous (fun q : EuclideanSpace ℝ ι × CovarianceMatrix ι => q.2.val i j) :=
      (show Continuous (fun q : EuclideanSpace ℝ ι × CovarianceMatrix ι => q.2.val) from
        continuous_subtype_val.comp continuous_snd).matrix_elem i j
    have hi : Continuous (fun q : EuclideanSpace ℝ ι × CovarianceMatrix ι => inner ℝ t q.1) :=
      continuous_const.inner continuous_fst
    exact ((Complex.continuous_ofReal.comp hi).mul continuous_const |>.sub
      ((Complex.continuous_ofReal.comp (continuous_finsetSum _ fun i _ => continuous_const.mul
        (continuous_finsetSum _ fun j _ => (he i j).mul continuous_const))).div_const 2)).cexp
  exact hc.continuousAt.tendsto.comp hp

lemma gaussianCovariance_integral_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : EuclideanSpace ℝ ι →ᵇ ℝ) :
    Continuous (fun p : EuclideanSpace ℝ ι × CovarianceMatrix ι =>
      ∫ x, f x ∂multivariateGaussian p.1 p.2.val) :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp gaussianCovarianceLaw_continuous

lemma gaussianCovariance_integral_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ → EuclideanSpace ℝ ι} {m₀ : EuclideanSpace ℝ ι}
    {C : ℕ → CovarianceMatrix ι} {C₀ : CovarianceMatrix ι}
    (hm : Tendsto m atTop (𝓝 m₀)) (hC : Tendsto C atTop (𝓝 C₀))
    (f : EuclideanSpace ℝ ι →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f x ∂multivariateGaussian (m n) (C n).val) atTop
      (𝓝 (∫ x, f x ∂multivariateGaussian m₀ C₀.val)) :=
  (gaussianCovariance_integral_continuous f).continuousAt.tendsto.comp (hm.prodMk_nhds hC)

end SphericalPerceptron
end
end
end

end OAI
