import OAI.Probability.InvariantIsing.Fields.CanonicalSpinWeights
import OAI.Probability.InvariantIsing.Fields.FieldProjectionMean

namespace OAI

/-! Independent endpoint fields followed by their Gibbs spin draws have
the product of the averaged one-site spin laws. This identifies the
projection-distance average appearing in the terminal-loss estimate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma scalarSpinKernel_atom_integrable (ν : Measure ℝ) [IsFiniteMeasure ν] (b : Bool) :
    Integrable (fun z => (scalarSpinKernel z).real {b}) ν := by
  have hm : Measurable (fun z => (scalarSpinKernel z).real {b}) :=
    (scalarSpinKernel.measurable_coe (measurableSet_singleton b)).ennreal_toReal
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  have he := ENNReal.toReal_mono
    (measure_ne_top (scalarSpinKernel z) Set.univ)
    (measure_mono (Set.subset_univ ({b} : Set Bool)))
  simpa only [measure_univ, ENNReal.toReal_one, measureReal_def] using he

lemma scalarSpinKernel_average_atom (ν : Measure ℝ) [IsProbabilityMeasure ν] (b : Bool) :
    (∫ z, (scalarSpinKernel z).real {b} ∂ν) = (scalarSpinKernel ∘ₘ ν).real {b} := by
  let A : Bool → ℝ := Set.indicator {b} 1
  have he : (∫ σ, A σ ∂(scalarSpinKernel ∘ₘ ν)) =
      ∫ z, ∫ σ, A σ ∂scalarSpinKernel z ∂ν := by
    rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (Integrable.of_finite)]
    rfl
  have hp (z : ℝ) : (∫ σ, A σ ∂scalarSpinKernel z) = (scalarSpinKernel z).real {b} :=
    integral_indicator_one (μ := scalarSpinKernel z) (measurableSet_singleton b)
  simp_rw [hp] at he
  exact he.symm.trans (integral_indicator_one (μ := scalarSpinKernel ∘ₘ ν)
    (measurableSet_singleton b))

theorem field_product_spin_average {N : ℕ} (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (A : Spin N → ℝ) :
    (∫ z : Fin N → ℝ, ∑ σ, finiteCanonicalWeights (fieldEnergy z) σ * A σ ∂Measure.pi ν) =
      ∫ σ : Spin N, A σ ∂Measure.pi (fun i => scalarSpinKernel ∘ₘ ν i) := by
  have hp (σ : Spin N) : Integrable (fun z : Fin N → ℝ =>
      finiteCanonicalWeights (fieldEnergy z) σ) (Measure.pi ν) := by
    have hi := Integrable.fintype_prod_dep (fun i => scalarSpinKernel_atom_integrable (ν i) (σ i))
    simpa only [fieldCanonicalWeights_product] using hi
  rw [integral_finsetSum _ (fun σ _ => (hp σ).mul_const (A σ)), integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro σ _
  rw [integral_mul_const]
  have he : (∫ z : Fin N → ℝ, finiteCanonicalWeights (fieldEnergy z) σ ∂Measure.pi ν) =
      (∏ i, (scalarSpinKernel ∘ₘ ν i).real {σ i}) := by
    simp_rw [fieldCanonicalWeights_product]
    change (∫ z : Fin N → ℝ, ∏ i,
      (fun y : ℝ => (scalarSpinKernel y).real {σ i}) (z i) ∂Measure.pi ν) = _
    rw [integral_fintype_prod_eq_prod (fun i y => (scalarSpinKernel y).real {σ i})]
    simp_rw [scalarSpinKernel_average_atom]
  rw [he]
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod, smul_eq_mul]

end InvariantIsing

end

end OAI
