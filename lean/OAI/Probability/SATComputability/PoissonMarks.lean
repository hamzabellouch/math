import OAI.Probability.DilutedSpin.FinitePoissonSplit

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem uniform_poisson_marks {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    (r : ℝ≥0) (V : A → E) :
    compoundPoisson r (Measure.map V (finiteUniform A)) =
      Measure.map (fun x : A → E => ∑ a, x a)
        (Measure.pi (fun a => compoundPoisson (r / Fintype.card A) (Measure.dirac (V a)))) := by
  have hV : Measurable V := measurable_of_countable V
  let : IsProbabilityMeasure (Measure.map V (finiteUniform A)) :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr inferInstance
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_compoundPoisson, charFunDual_map_sum_pi_eq_prod]
  simp only [Finset.prod_apply]
  simp_rw [charFunDual_compoundPoisson, charFunDual_apply, integral_dirac]
  rw [← Complex.exp_sum]
  congr 1
  rw [integral_map hV.aemeasurable (by fun_prop), integral_finiteUniform]
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [NNReal.coe_div, NNReal.coe_natCast, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.real_smul, Complex.ofReal_inv]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  simp only [mul_comm Complex.I]

end FixedClauseThreshold.Computability

end OAI
