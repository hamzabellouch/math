import Mathlib
import OAI.Probability.Ballisticity.Estimates.SelectedEndpointMoment
import OAI.Probability.Ballisticity.Walk.SelectedFiniteKernel

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma normalizeFinite_map {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) (Y : Ω → A) (hY : Measurable Y) :
    normalizeFinite (μ.map Y) = (normalizeFinite μ).map Y := by
  simp only [normalizeFinite,Measure.map_apply hY MeasurableSet.univ,Set.preimage_univ,
    Measure.map_smul _ hY.aemeasurable]

lemma normalizeFinite_restrict {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Set Ω) : normalizeFinite (μ.restrict N) = μ[|N] := by
  simp only [normalizeFinite,Measure.restrict_apply_univ,ProbabilityTheory.cond]

lemma selectedFiniteKernel_map_eq {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure Ω) (N : Set Ω) (Z : Ω → A) (hZ : Measurable Z)
    (E : Set A) (hE : MeasurableSet E) (Y : A → ℝ) (hY : Measurable Y)
    (dummy : A) (failure strict : Prop) [Decidable failure] [Decidable strict] :
    (selectedFiniteKernel ((μ.restrict N).map Z) E dummy failure strict).map Y =
      selectedEndpointLaw μ N (N ∩ Z ⁻¹' E) (Y ∘ Z) (Y dummy) failure strict := by
  by_cases hf : failure
  · simp only [selectedFiniteKernel,selectedEndpointLaw,ite_eq_left hf,Measure.map_dirac' hY]
  simp only [selectedFiniteKernel,selectedEndpointLaw,ite_eq_right hf]
  by_cases hs : strict
  · simp only [ite_eq_left hs]
    rw [Measure.restrict_map hZ hE,Measure.restrict_restrict (hZ hE)]
    rw [Set.inter_comm (Z ⁻¹' E) N,normalizeFinite_map _ Z hZ,
      normalizeFinite_restrict,Measure.map_map hY hZ]
  · simp only [ite_eq_right hs]
    rw [normalizeFinite_map _ Z hZ,normalizeFinite_restrict,Measure.map_map hY hZ]

lemma selectedEndpointLaw_cond {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (C N E : Set Ω)
    (hC : MeasurableSet C) (hN : MeasurableSet N) (hE : MeasurableSet E)
    (Y : Ω → ℝ) (b : ℝ) (failure strict : Prop) [Decidable failure] [Decidable strict] :
    selectedEndpointLaw μ[|C] N E Y b failure strict =
      selectedEndpointLaw μ (C ∩ N) (C ∩ E) Y b failure strict := by
  unfold selectedEndpointLaw
  split_ifs with hf hs
  · rfl
  · rw [cond_cond_eq_cond_inter hC hE]
  · rw [cond_cond_eq_cond_inter hC hN]

end DirectionalTransience

end

end

end OAI
