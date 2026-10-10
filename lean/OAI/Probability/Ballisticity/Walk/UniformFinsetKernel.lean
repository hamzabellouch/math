import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience

lemma uniformFinset_eq {B : Type*} [MeasurableSpace B] [Countable B]
    [MeasurableSingletonClass B] (s : Finset B) (hs : s.Nonempty) :
    (PMF.uniformOfFinset s hs).toMeasure = (s.card:ℝ≥0∞)⁻¹ • ∑ b∈s, Measure.dirac b := by
  apply Measure.ext_of_singleton
  intro b
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),PMF.uniformOfFinset_apply,
    Measure.smul_apply,Measure.finsetSum_apply]
  simp only [Measure.dirac_apply' _ (measurableSet_singleton b),smul_eq_mul]
  by_cases hb : b∈s
  · simp [hb]
  · simp [hb]

lemma uniformFinset_map {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    [Countable B] [Countable C] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (s : Finset B) (t : Finset C) (hs : s.Nonempty) (ht : t.Nonempty) (f : B → C)
    (hi : Set.InjOn f s) (he : s.image f=t) :
    ((PMF.uniformOfFinset s hs).toMeasure).map f=(PMF.uniformOfFinset t ht).toMeasure := by
  have hc : s.card=t.card := by rw [←he,Finset.card_image_iff.mpr hi]
  rw [uniformFinset_eq s hs,uniformFinset_eq t ht,
    Measure.map_smul _ (measurable_of_countable f).aemeasurable,
    Measure.map_finset_sum (measurable_of_countable f).aemeasurable,hc]
  simp only [Measure.map_dirac]
  congr 1
  rw [←he,Finset.sum_image hi]

noncomputable def nonemptyFinsetKernel {B : Type*} [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B] : Kernel {t : Finset B | t.Nonempty} B :=
  Kernel.ofFunOfCountable (fun t => (PMF.uniformOfFinset t.1 t.2).toMeasure)

noncomputable def uniformFinsetKernel {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B] (s : A → Finset B)
    (hm : Measurable s) (hs : ∀ a, (s a).Nonempty) : Kernel A B :=
  nonemptyFinsetKernel.comap (fun a => ⟨s a,hs a⟩) (hm.subtype_mk (h := hs))

instance uniformFinsetKernel_markov {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B] (s : A → Finset B)
    (hm : Measurable s) (hs : ∀ a, (s a).Nonempty) :
    IsMarkovKernel (uniformFinsetKernel s hm hs) where
  isProbabilityMeasure a := by change IsProbabilityMeasure (PMF.uniformOfFinset (s a) (hs a)).toMeasure; infer_instance

lemma uniformFinsetKernel_supported {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B] (s : A → Finset B)
    (hm : Measurable s) (hs : ∀ a, (s a).Nonempty) (a : A) :
    ∀ᵐ b ∂uniformFinsetKernel s hm hs a, b∈s a := by
  rw [ae_iff]
  change (PMF.uniformOfFinset (s a) (hs a)).toMeasure {b | b∉s a}=0
  rw [PMF.toMeasure_uniformOfFinset_apply (hs a) _ (Set.to_countable _).measurableSet]
  simp

end DirectionalTransience

end

end OAI
