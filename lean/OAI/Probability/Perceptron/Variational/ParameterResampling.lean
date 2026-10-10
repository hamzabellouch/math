import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma infinitePi_update_measurePreserving {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (p : ℕ) :
    MeasurePreserving (fun a : (ℕ→X) × X => Function.update a.1 p a.2)
      ((Measure.infinitePi fun _ : ℕ => μ).prod μ) (Measure.infinitePi fun _ : ℕ => μ) := by
  classical
  refine ⟨by fun_prop,?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  by_cases hp : p∈s
  · have he : (fun a : (ℕ→X) × X => Function.update a.1 p a.2) ⁻¹' Set.pi s t =
        (Set.pi (s.erase p) t) ×ˢ t p := by
      ext a
      simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Finset.mem_coe,Finset.mem_erase]
      constructor
      · intro h
        refine ⟨fun i hi => ?_,?_⟩
        · simpa only [Function.update_of_ne hi.1] using h i hi.2
        · simpa only [Function.update_self] using h p hp
      · rintro ⟨ha,hb⟩ i hi
        by_cases hip : i=p
        · subst i; simpa only [Function.update_self] using hb
        · simpa only [Function.update_of_ne hip] using ha i ⟨hip,hi⟩
    rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun i _ => ht i)]
    exact Finset.prod_erase_mul _ _ hp
  · have he : (fun a : (ℕ→X) × X => Function.update a.1 p a.2) ⁻¹' Set.pi s t =
        (Set.pi s t) ×ˢ (univ : Set X) := by
      ext a
      simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Set.mem_univ,and_true,Finset.mem_coe]
      exact forall_congr' fun i => by
        by_cases hi : i∈s
        · have hip : i≠p := fun h => hp (h ▸ hi)
          simp only [hi,true_implies,Function.update_of_ne hip]
        · simp only [hi,false_implies]
    rw [he,Measure.prod_prod,measure_univ,mul_one,Measure.infinitePi_pi _ (fun i _ => ht i)]

def bulkParameterUniform : Measure ℝ := volume.restrict (Ioc (1:ℝ) 2)

instance : IsProbabilityMeasure bulkParameterUniform := ⟨by norm_num [bulkParameterUniform]⟩

def bulkParameterLaw : Measure (ℕ→ℝ) := Measure.infinitePi fun _ : ℕ => bulkParameterUniform

instance : IsProbabilityMeasure bulkParameterLaw := by unfold bulkParameterLaw; infer_instance

lemma bulkParameterLaw_ae : ∀ᵐ v ∂bulkParameterLaw, ∀ j, v j∈Icc (1:ℝ) 2 := by
  rw [ae_all_iff]
  intro j
  have he : ∀ᵐ x ∂bulkParameterUniform, x∈Icc (1:ℝ) 2 :=
    (ae_restrict_mem measurableSet_Ioc).mono fun _ hx => ⟨hx.1.le,hx.2⟩
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => bulkParameterUniform) j).quasiMeasurePreserving.ae he

lemma bulkParameterLaw_integral_resample (p : ℕ) {F : (ℕ→ℝ)→ℝ}
    (hF : Integrable F bulkParameterLaw) :
    (∫ v, F v ∂bulkParameterLaw) = ∫ v, (∫ u in (1:ℝ)..2,
      F (Function.update v p u)) ∂bulkParameterLaw := by
  have hm := infinitePi_update_measurePreserving bulkParameterUniform p
  change MeasurePreserving (fun a : (ℕ→ℝ) × ℝ => Function.update a.1 p a.2)
    (bulkParameterLaw.prod bulkParameterUniform) bulkParameterLaw at hm
  have hi : Integrable (fun a : (ℕ→ℝ) × ℝ => F (Function.update a.1 p a.2))
      (bulkParameterLaw.prod bulkParameterUniform) := hm.integrable_comp hF.aestronglyMeasurable |>.mpr hF
  calc
    _ = ∫ a : (ℕ→ℝ) × ℝ, F (Function.update a.1 p a.2) ∂(bulkParameterLaw.prod bulkParameterUniform) :=
      by
        have hh : AEStronglyMeasurable F (Measure.map (fun a : (ℕ→ℝ) × ℝ => Function.update a.1 p a.2)
            (bulkParameterLaw.prod bulkParameterUniform)) := by rw [hm.map_eq]; exact hF.aestronglyMeasurable
        simpa only [hm.map_eq] using integral_map hm.measurable.aemeasurable hh
    _ = ∫ v, ∫ u, F (Function.update v p u) ∂bulkParameterUniform ∂bulkParameterLaw := integral_prod _ hi
    _ = _ := by simp only [bulkParameterUniform,intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2)]

end SphericalPerceptronFreeEnergy
end

end OAI
