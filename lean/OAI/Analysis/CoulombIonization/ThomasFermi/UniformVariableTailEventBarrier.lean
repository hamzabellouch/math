import Mathlib
import OAI.Analysis.CoulombIonization.Localization.UniformDyadicEvent
import OAI.Analysis.CoulombIonization.ThomasFermi.UniformFamilyEventBarrier
import OAI.Analysis.CoulombIonization.Localization.TailObservationEventBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator quantumEventMultiplier

theorem quantum_uniform_near_minimizer_variable_tail_event_tilt {Z r : ℝ} (hZ : 0 ≤ Z)
    (hr : 0 < r) (N K : ℕ) (p₀ : Fin (K+1) → ℝ) {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (j : Fin (K+1)) (A : Set (Fin K × (Fin N × Fin 3) → ℝ))
        (_hA : MeasurableSet[arrayObservationInformation N K j] A),
        p₀ j ≤ physicalObservationProbability F (fun k : Fin K => dyadicObservationWidth r k) A →
      ∃ G : fermionGraph N,
        ‖fermionGraphValue N G‖^2 = 1 ∧
        graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F
          (fun k : Fin K => dyadicObservationWidth r k) A))⁻¹ •
          Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
            (physicalObservationEvent (fun k : Fin K => dyadicObservationWidth r k) A)) ∧
        formEnergy Z (graphFormVector G) ≤ energy Z N+
          observationFisherConstant*((2:ℝ)^j.val*r)^(-2.02:ℝ)*
            (Real.log (Real.exp 1/physicalObservationProbability F
              (fun k : Fin K => dyadicObservationWidth r k) A))^5+δ := by
  let ell : Fin K → ℝ := fun k : Fin K => dyadicObservationWidth r k
  let b : Fin (K+1) → Fin K → ℝ := fun j => tailObservationCoefficient ell j
  have hell k : 0 < ell k := dyadicObservationWidth_pos hr k
  apply Exists.imp (p := fun F : fermionGraph N =>
      ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (i : Fin (K+1)) (A : Set (Fin K × (Fin N × Fin 3) → ℝ))
        (_hA : MeasurableSet A) (_hsy : QuantumEventSymmetric A),
        p₀ i ≤ quantumEventProbability F (b i) A →
      ∃ G : fermionGraph N,
        ‖fermionGraphValue N G‖^2 = 1 ∧
        graphRawLaw G = (ENNReal.ofReal (quantumEventProbability F (b i) A))⁻¹ •
          Measure.map Prod.fst
            (((graphRawLaw F).prod
              (Measure.pi (fun _ : Fin K × (Fin N × Fin 3) => compactNoiseLaw))).restrict
                (quantumObservationEvent (b i) A)) ∧
        formEnergy Z (graphFormVector G) ≤ energy Z N +
          (observationFisherConstant/2)*(∑ k, (b i k)^2)*
            (Real.log (Real.exp 1/quantumEventProbability F (b i) A))^5+δ)
  · intro F h
    refine ⟨h.1,h.2.1,?_⟩
    intro j A hA hp
    have hm := arrayObservationInformation_le N K j A hA
    have hsy := arrayObservationInformation_le_symmetric N K j A hA
    have hm' := hm.preimage (scaleObservationArray ell).measurable
    have hid := tail_quantumEventProbability_eq_physical F h.1 ell hell j hA
    have hp' : p₀ j ≤ quantumEventProbability F (b j) (scaleObservationArray ell ⁻¹' A) := by
      rwa [hid]
    obtain ⟨G,hG,hlaw,hcost⟩ := h.2.2 j _ hm' (scaledObservationEvent_symmetric ell hsy) hp'
    change quantumEventProbability F (b j) _ = _ at hid
    rw [hid,tail_physicalObservationEvent_eq ell hell j hA] at hlaw
    rw [hid] at hcost
    refine ⟨G,hG,hlaw,hcost.trans ?_⟩
    have hc := tail_observationTiltEnergyCost_dyadic hr ((h₀ j).trans_le hp)
      (physicalObservationProbability_le_one F h.1 ell A) j K
    exact add_le_add (add_le_add le_rfl hc) le_rfl
  · exact quantum_uniform_near_minimizer_family_variable_event_tilt hZ N b p₀ h₀ hδ
end CoulombAtom

end

end OAI
