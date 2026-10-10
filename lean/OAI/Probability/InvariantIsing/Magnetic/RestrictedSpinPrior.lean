import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinBias
import OAI.Probability.InvariantIsing.Fields.PriorSpinLeafConditioning

namespace OAI

/-! A normalized constrained prior gives exactly the conditional Gibbs
law. Its log normalizer retains the original cube mass as an explicit
constant. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def restrictedSpinPrior {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    ProbabilityMeasure (Spin N) :=
  ⟨restrictedSpinLaw S (fun _ => 0), restrictedSpinLaw_probability S hS _⟩

lemma restrictedSpinPrior_singleton {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (σ : Spin N) : (restrictedSpinPrior S hS : Measure (Spin N)).real {σ} =
      if σ ∈ S then (S.card : ℝ)⁻¹ else 0 := by
  have hm := restrictedSpinLaw_mass S hS (fun _ => 0) {σ}
  simp only [Finset.coe_singleton] at hm
  change (restrictedSpinLaw S (fun _ => 0)).real {σ} = _
  rw [hm]
  by_cases hσ : σ ∈ S <;> simp [hσ]

lemma integral_restrictedSpinPrior {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (f : Spin N → ℝ) :
    (∫ σ, f σ ∂(restrictedSpinPrior S hS : Measure (Spin N))) =
      (S.card : ℝ)⁻¹ * ∑ σ ∈ S, f σ := by
  rw [integral_fintype (Integrable.of_finite)]
  simp_rw [restrictedSpinPrior_singleton, smul_eq_mul, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

lemma finiteLogIntegral_restrictedSpinPrior {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) :
    finiteLogIntegral (restrictedSpinPrior S hS : Measure (Spin N)) H =
      restrictedSpinLog S H - (Real.log S.card - N * Real.log 2) := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  rw [finiteLogIntegral, integral_restrictedSpinPrior, Real.log_mul
    (inv_pos.mpr hcard).ne' (Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS).ne', Real.log_inv]
  unfold restrictedSpinLog
  ring

lemma integral_restrictedSpinPrior_gibbs {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H f : Spin N → ℝ) :
    (∫ σ, f σ ∂gibbsProbability (restrictedSpinPrior S hS : Measure (Spin N)) H) =
      (∑ σ ∈ S, Real.exp (H σ) * f σ) / ∑ σ ∈ S, Real.exp (H σ) := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  rw [gibbsProbability_eq_tilted _ _ Integrable.of_finite, integral_tilted,
    integral_restrictedSpinPrior, integral_restrictedSpinPrior]
  simp only [smul_eq_mul, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  field_simp

lemma gibbsProbability_restrictedSpinPrior {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) :
    gibbsProbability (restrictedSpinPrior S hS : Measure (Spin N)) H = restrictedSpinLaw S H := by
  let _ := restrictedSpinLaw_probability S hS H
  apply Measure.ext_of_singleton
  intro σ
  have he : (gibbsProbability (restrictedSpinPrior S hS : Measure (Spin N)) H).real {σ} =
      (restrictedSpinLaw S H).real {σ} := by
    rw [← integral_indicator_one (measurableSet_singleton σ), integral_restrictedSpinPrior_gibbs]
    have hm := restrictedSpinLaw_mass S hS H {σ}
    simp only [Finset.coe_singleton] at hm
    rw [hm]
    simp only [Set.indicator, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
    by_cases hσ : σ ∈ S <;> simp [hσ]
  have hh := congrArg ENNReal.ofReal he
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh

end InvariantIsing

end

end OAI
