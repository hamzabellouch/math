import Mathlib
import OAI.Analysis.HardSphere.Comparison.TaggedMoment

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I X : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X]

def retainedFiniteSum (P : I→Measure X) : Measure (I×X) :=
  ∑i,(P i).map (Prod.mk i)
instance retainedFiniteSum_finite (P : I→Measure X) [∀i,IsFiniteMeasure (P i)] :
    IsFiniteMeasure (retainedFiniteSum P) := by
  unfold retainedFiniteSum; infer_instance
omit [MeasurableSingletonClass I] in
lemma retainedFiniteSum_snd (P : I→Measure X) :
    (retainedFiniteSum P).map Prod.snd=∑i,P i := by
  simp only [retainedFiniteSum,Measure.map_finset_sum' measurable_snd.aemeasurable,
    Measure.map_map measurable_snd measurable_prodMk_left,Function.comp_def,Measure.map_id']

lemma retainedFiniteSum_density (P ν : I→Measure X) [∀i,IsFiniteMeasure (P i)]
    [∀i,IsFiniteMeasure (ν i)] (ha : ∀i,ν i≪P i) :
    retainedFiniteSum ν=(retainedFiniteSum P).withDensity (fun z ↦ (ν z.1).rnDeriv (P z.1) z.2) := by
  let F : I×X→ℝ≥0∞ := fun z ↦ (ν z.1).rnDeriv (P z.1) z.2
  have hF : Measurable F := taggedFunction_measurable _ (fun i ↦ Measure.measurable_rnDeriv _ _)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul _ hF hf]
  simp only [retainedFiniteSum,lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_map hf measurable_prodMk_left,lintegral_map (hF.mul hf) measurable_prodMk_left]
  have he := Measure.withDensity_rnDeriv_eq (ν i) (P i) (ha i)
  rw [←he]
  exact lintegral_withDensity_eq_lintegral_mul _ (Measure.measurable_rnDeriv _ _)
    (show Measurable (fun x ↦ f (i,x)) from hf.comp measurable_prodMk_left)

theorem finite_sum_second_moment (P ν : I→Measure X) [∀i,IsFiniteMeasure (P i)]
    [∀i,IsFiniteMeasure (ν i)] (ha : ∀i,ν i≪P i)
    (hi : ∀i,Integrable (fun x ↦ ((ν i).rnDeriv (P i) x).toReal^2) (P i)) :
    Integrable (fun x ↦ ((∑i,ν i).rnDeriv (∑i,P i) x).toReal^2) (∑i,P i) ∧
    (∫x,((∑i,ν i).rnDeriv (∑i,P i) x).toReal^2 ∂(∑i,P i))≤
      ∑i,∫x,((ν i).rnDeriv (P i) x).toReal^2 ∂P i := by
  let F : I×X→ℝ≥0∞ := fun z ↦ (ν z.1).rnDeriv (P z.1) z.2
  have hF : Measurable F := taggedFunction_measurable _ (fun i ↦ Measure.measurable_rnDeriv _ _)
  have hfs := hF.ennreal_toReal.pow_const 2
  have hiF : ∀i,Integrable (fun z ↦ (F z).toReal^2) ((P i).map (Prod.mk i)) := by
    intro i
    exact (integrable_map_measure hfs.aestronglyMeasurable measurable_prodMk_left.aemeasurable).mpr (hi i)
  have hiR : Integrable (fun z ↦ (F z).toReal^2) (retainedFiniteSum P) :=
    integrable_finsetSum_measure.mpr (fun i _ ↦ hiF i)
  have hd := retainedFiniteSum_density P ν ha
  have he : (fun z ↦ ((retainedFiniteSum ν).rnDeriv (retainedFiniteSum P) z).toReal^2)=ᵐ[retainedFiniteSum P]
      (fun z ↦ (F z).toReal^2) := by
    rw [hd]
    exact (Measure.rnDeriv_withDensity _ hF).fun_comp (fun a : ℝ≥0∞ ↦ a.toReal^2)
  have hac : retainedFiniteSum ν≪retainedFiniteSum P := by
    rw [hd]; exact withDensity_absolutelyContinuous _ _
  have H := observed_second_moment (retainedFiniteSum P) (retainedFiniteSum ν) hac
    Prod.snd measurable_snd (hiR.congr he.symm)
  simp only [retainedFiniteSum_snd] at H
  refine ⟨H.1,H.2.trans_eq ?_⟩
  rw [integral_congr_ae he,retainedFiniteSum,integral_finsetSum_measure (fun i _ ↦ hiF i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_map measurable_prodMk_left.aemeasurable hfs.aestronglyMeasurable

end HardSphere.Comparison
end
end

end OAI
