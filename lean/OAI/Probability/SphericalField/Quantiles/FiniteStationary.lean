import Mathlib
import OAI.Probability.SphericalField.Fields.FiniteModels
import OAI.Probability.SphericalField.Quantiles.Distribution

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def FiniteFieldModel.quantile {B : ℝ} {q : BoundedField B} (M : FiniteFieldModel q) (hB : B ≤ 1) :
    Fin (M.depth+1) → Time := fun i => ⟨M.value i,
      (M.values_mem (ae_of_all _ fun u => ⟨q.nonneg u,q.le_bound u⟩) i).1,
      (M.values_mem (ae_of_all _ fun u => ⟨q.nonneg u,q.le_bound u⟩) i).2.trans hB⟩

lemma FiniteFieldModel.quantile_monotone {B : ℝ} {q : BoundedField B} (M : FiniteFieldModel q) (hB : B ≤ 1) :
    Monotone (M.quantile hB) := fun _ _ h => M.monotone_value h

lemma FiniteFieldModel.quantile_lt_one {B : ℝ} {q : BoundedField B} (M : FiniteFieldModel q) (hB : B < 1)
    (i : Fin (M.depth+1)) : (M.quantile hB.le i:ℝ) < 1 :=
  (M.values_mem (ae_of_all _ fun u => ⟨q.nonneg u,q.le_bound u⟩) i).2.trans_lt hB

lemma FiniteFieldModel.quantileTrial_eq {B : ℝ} {q : BoundedField B} (M : FiniteFieldModel q) (hB : B ≤ 1) :
    quantileTrial (q.toQuantile hB)=weightedStepTrial M.weight (M.quantile hB)
      (fun i => (M.weight_pos i).le) M.weight_sum := by
  apply Trial.ext_fun
  intro t
  rw [quantileTrial_eq_integral _ (q.toQuantile_measurable hB)]
  change (∫ u, (if q u ≤ (t:ℝ) then (1:ℝ) else 0) ∂timeLaw)=_
  rw [M.integral (fun x => if x ≤ (t:ℝ) then 1 else 0)]
  change (∑ i, M.weight i*(if M.value i ≤ (t:ℝ) then 1 else 0))=∑ i, if M.value i ≤ (t:ℝ) then M.weight i else 0
  simp only [mul_ite,mul_one,mul_zero]

lemma FiniteFieldModel.quantileTail_eq {B : ℝ} {q : BoundedField B} (M : FiniteFieldModel q) (hB : B ≤ 1) (t : ℝ) :
    quantileTail (q.toQuantile hB) t=weightedStepTail M.weight M.value t :=
  M.integral (fun x => 1-max x t)

lemma FiniteFieldModel.quantileA_eq {B : ℝ} {q : BoundedField B} (M : FiniteFieldModel q) (hB : B ≤ 1) (r : ℝ) :
    quantileA (q.toQuantile hB) r=weightedStepA M.weight M.value r := by
  unfold quantileA weightedStepA
  simp_rw [M.quantileTail_eq hB]

def FiniteFieldModel.stationaryModel {B : ℝ} {q : BoundedField B} (M : FiniteFieldModel q) (hB : B < 1) :
    FiniteFieldModel (q.stationary hB) where
  depth := M.depth
  value := fun i => quantileA (q.toQuantile hB.le) (M.value i)/2
  label := M.label
  measurable_label := M.measurable_label
  positive := M.positive
  monotone_value := by
    intro i j hij
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply quantileA_mono _ (q.toQuantile_measurable hB.le) hB (ae_of_all _ q.le_bound)
      (M.values_mem (ae_of_all _ fun u => ⟨q.nonneg u,q.le_bound u⟩) i)
      (M.values_mem (ae_of_all _ fun u => ⟨q.nonneg u,q.le_bound u⟩) j)
    exact M.monotone_value hij
  agrees := by
    filter_upwards [M.agrees] with u hu
    change quantileA (q.toQuantile hB.le) (M.value (M.label u))/2=quantileA (q.toQuantile hB.le) (q u)/2
    rw [hu]

lemma FiniteFieldModel.stationary_minimum {B : ℝ} {q : BoundedField B} (M : FiniteFieldModel q) (hB : B < 1) :
    sInf (finiteSphericalDualValues (M.stationaryModel hB).weight (M.stationaryModel hB).value
      (fun i => ((M.stationaryModel hB).weight_pos i).le) (M.stationaryModel hB).weight_sum)=
      (entropy (quantileTrial (q.toQuantile hB.le))).toReal-∫ u, q.stationary hB u*q u ∂timeLaw := by
  let Q := M.quantile hB.le
  let F := M.stationaryModel hB
  have hstat (i : Fin (M.depth+1)) : 2*F.value i=weightedStepA M.weight (fun j => (Q j:ℝ)) (Q i) := by
    change 2*(quantileA (q.toQuantile hB.le) (M.value i)/2)=weightedStepA M.weight M.value (M.value i)
    rw [M.quantileA_eq hB.le]
    ring
  have hleast : IsLeast (finiteSphericalDualValues M.weight F.value (fun i => (M.weight_pos i).le) M.weight_sum)
      (finiteSphericalDualObjective M.weight F.value (fun i => (M.weight_pos i).le) M.weight_sum Q) := by
    refine ⟨⟨Q,⟨M.quantile_monotone hB.le,M.quantile_lt_one hB _⟩,rfl⟩,?_⟩
    rintro a ⟨p,⟨hp,hp1⟩,rfl⟩
    exact stationary_finite_entropy_minimizes M.weight F.value Q p (fun i => (M.weight_pos i).le) M.weight_sum
      (M.quantile_monotone hB.le) hp (M.quantile_lt_one hB _) hp1 hstat
  change sInf (finiteSphericalDualValues M.weight F.value _ _)=_
  rw [hleast.csInf_eq]
  unfold finiteSphericalDualObjective
  rw [← M.quantileTrial_eq hB.le]
  congr 1
  change (∑ i, M.weight i*(quantileA (q.toQuantile hB.le) (M.value i)/2)*M.value i)=
    ∫ u, (quantileA (q.toQuantile hB.le) (q u)/2)*q u ∂timeLaw
  rw [M.integral (fun x => (quantileA (q.toQuantile hB.le) x/2)*x)]
  apply Finset.sum_congr rfl
  intro i _
  ring

end SphericalPerceptron
end
end

end OAI
