import Mathlib

namespace OAI

section
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The law of the sum of iid marks with an independent Poisson count. -/
noncomputable def compoundPoisson (r : ℝ≥0) (μ : Measure E) : Measure E :=
  Measure.sum (fun n : ℕ => ENNReal.ofReal (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial) •
    Measure.map (fun x : Fin n → E => ∑ i, x i) (Measure.pi (fun _ : Fin n => μ)))

instance compoundPoisson_prob (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (compoundPoisson r μ) := by
  constructor
  have hh := (hasSum_one_poissonMeasure r).tsum_eq
  rw [compoundPoisson,Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hasSum_one_poissonMeasure r).summable,hh]
  norm_num

lemma charFunDual_iid_sum (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (L : StrongDual ℝ E) :
    charFunDual (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) L =
      charFunDual μ L ^ n := by
  rw [charFunDual_apply,integral_map (by fun_prop) (by fun_prop)]
  simp_rw [map_sum,Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin n => fun x : E => Complex.exp ((L x : ℂ)*Complex.I))]
  simp only [charFunDual_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma charFunDual_compoundPoisson (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : StrongDual ℝ E) :
    charFunDual (compoundPoisson r μ) L = Complex.exp ((r:ℂ)*(charFunDual μ L-1)) := by
  have hi : Integrable (fun x : E => Complex.exp ((L x:ℂ)*Complex.I)) (compoundPoisson r μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  change (∫ x, Complex.exp ((L x:ℂ)*Complex.I) ∂compoundPoisson r μ) = _
  rw [compoundPoisson,integral_sum_measure hi]
  have hw (n : ℕ) : 0 ≤ Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial := by positivity
  simp_rw [integral_smul_measure,ENNReal.toReal_ofReal (hw _)]
  change (∑' n : ℕ, (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial) •
    charFunDual (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) L) = _
  simp_rw [charFunDual_iid_sum,Complex.real_smul]
  have hh := (NormedSpace.expSeries_div_hasSum_exp ((r:ℂ)*charFunDual μ L)).mul_left
    (Complex.exp (-(r:ℂ)))
  have he : (fun n : ℕ => ((Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial:ℝ):ℂ)*charFunDual μ L^n) =
      (fun n : ℕ => Complex.exp (-(r:ℂ))*(((r:ℂ)*charFunDual μ L)^n/n.factorial)) := by
    funext n
    simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,
      Complex.ofReal_exp,Complex.ofReal_neg,mul_pow]
    ring
  rw [he,hh.tsum_eq]
  rw [← Complex.exp_eq_exp_ℂ,← Complex.exp_add]
  congr 1
  ring
end DilutedSpinGlass

end

end OAI
