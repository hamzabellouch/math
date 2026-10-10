import Mathlib
import OAI.Probability.Perceptron.Cascade.WeightedCDF
import OAI.Probability.Perceptron.Variational.FieldRounding

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def weightedTrialLaw {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time) : Measure Time :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (q i)

lemma weightedTrialLaw_probability {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) : IsProbabilityMeasure (weightedTrialLaw w q) := by
  constructor
  simp only [weightedTrialLaw,Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply_of_mem
    (mem_univ _),smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),hw1,ENNReal.ofReal_one]

lemma weightedTrialLaw_integral {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (g : Time→ℝ) :
    (∫ x, g x ∂weightedTrialLaw w q)=∑ i, w i*g (q i) := by
  unfold weightedTrialLaw
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (hw _),smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

lemma weightedTrialLaw_Iic {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (t : Time) :
    (weightedTrialLaw w q).real (Iic t)=∑ i, if q i≤t then w i else 0 := by
  simp only [weightedTrialLaw,Measure.real,Measure.finsetSum_apply,Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iic,smul_eq_mul,Set.indicator_apply,mem_Iic,Pi.one_apply]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [ENNReal.toReal_ofReal (hw i)]
  · intro i _
    split_ifs <;> simp

lemma quantileTrial_weightedTrialLaw {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) :
    quantileTrial (boundedQuantile (weightedTrialLaw w q))=weightedStepTrial w q hw hw1 := by
  have := weightedTrialLaw_probability w q hw hw1
  apply Trial.ext_fun
  intro t
  change (timeLaw {u | boundedQuantile (weightedTrialLaw w q) u≤t}).toReal=_
  have he := congrArg (fun μ : Measure Time => μ (Iic t)) (boundedQuantile_law (weightedTrialLaw w q))
  rw [Measure.map_apply (boundedQuantile_measurable _) measurableSet_Iic] at he
  change (timeLaw {u | boundedQuantile (weightedTrialLaw w q) u≤t})=_ at he
  rw [he]
  exact weightedTrialLaw_Iic w q hw t

end SphericalPerceptronFreeEnergy
end

end OAI
