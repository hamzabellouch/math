import OAI.Probability.SATComputability.PoissonMarks

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

theorem compoundPoisson_dirac_nsmul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (r : ℝ≥0) (v : E) :
    compoundPoisson r (Measure.dirac v) =
      Measure.map (fun m : ℕ => m • v) (poissonMeasure r) := by
  rw [compoundPoisson, poissonMeasure,
    Measure.map_sum (measurable_of_countable _).aemeasurable]
  congr 1
  funext m
  rw [Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_dirac' (measurable_of_countable _)]
  congr 1
  have ha : ∀ᵐ x ∂Measure.pi (fun _ : Fin m => Measure.dirac v), ∀ i, x i = v :=
    Filter.eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin m => Measure.dirac v) (i := i)).eventually
        (show ∀ᵐ x ∂Measure.dirac v, x = v from by simp))
  rw [Measure.map_congr (ha.mono (fun x hx =>
    show (∑ i, x i) = m • v by simp only [hx, Finset.sum_const, Finset.card_univ, Fintype.card_fin]))]
  simp

theorem uniform_poisson_count_vector {A : Type*} [Fintype A] [Nonempty A]
    [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (r : ℝ≥0) :
    compoundPoisson r (Measure.map (fun a : A => Pi.single a (1 : ℝ)) (finiteUniform A)) =
      Measure.map (fun counts : A → ℕ => fun a => (counts a : ℝ))
        (Measure.pi (fun _ : A => poissonMeasure (r / Fintype.card A))) := by
  rw [uniform_poisson_marks]
  simp_rw [compoundPoisson_dirac_nsmul]
  rw [← Measure.pi_map_pi (μ := fun _ : A => poissonMeasure (r / Fintype.card A))
    (f := fun a (m : ℕ) => m • (Pi.single a (1 : ℝ) : A → ℝ)) (fun a : A =>
    (measurable_of_countable (fun m : ℕ => m • (Pi.single a (1 : ℝ) : A → ℝ))).aemeasurable)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext counts a
  simp [Finset.sum_apply, Pi.single_apply]

theorem uniform_poisson_weighted_counts {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E] (r : ℝ≥0) (V : A → E) :
    compoundPoisson r (Measure.map V (finiteUniform A)) =
      Measure.map (fun counts : A → ℕ => ∑ a, counts a • V a)
        (Measure.pi (fun _ : A => poissonMeasure (r / Fintype.card A))) := by
  rw [uniform_poisson_marks]
  simp_rw [compoundPoisson_dirac_nsmul]
  rw [← Measure.pi_map_pi (μ := fun _ : A => poissonMeasure (r / Fintype.card A))
    (f := fun a (m : ℕ) => m • V a) (fun a =>
      (measurable_of_countable (fun m : ℕ => m • V a)).aemeasurable)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end FixedClauseThreshold.Computability

end OAI
