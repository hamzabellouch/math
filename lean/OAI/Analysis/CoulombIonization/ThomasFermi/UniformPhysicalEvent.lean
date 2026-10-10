import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.PricedSelectedMaster
import OAI.Analysis.CoulombIonization.Localization.UniformApproximateEvent

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

theorem quantum_uniform_near_minimizer_physical_event_tilt {Z : ℝ} (hZ : 0 ≤ Z)
    (N K : ℕ) (ell : Fin K → ℝ) (hell : ∀ k, 0 < ell k)
    {p₀ δ : ℝ} (h₀ : 0 < p₀) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (A : Set (Fin K × (Fin N × Fin 3) → ℝ)) (_hA : MeasurableSet A)
        (_hsy : QuantumEventSymmetric A), p₀ ≤ physicalObservationProbability F ell A →
      ∃ G : fermionGraph N,
        ‖fermionGraphValue N G‖^2 = 1 ∧
        graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell A))⁻¹ •
          Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
            (physicalObservationEvent ell A)) ∧
        formEnergy Z (graphFormVector G) ≤ energy Z N+
          observationTiltEnergyCost ell (physicalObservationProbability F ell A)+δ := by
  apply Exists.imp (p := fun F : fermionGraph N =>
      ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (A : Set (Fin K × (Fin N × Fin 3) → ℝ)) (_hA : MeasurableSet A)
        (_hsy : QuantumEventSymmetric A),
        p₀ ≤ quantumEventProbability F (fun k => (ell k)⁻¹) A →
      ∃ G : fermionGraph N,
        ‖fermionGraphValue N G‖^2 = 1 ∧
        graphRawLaw G =
          (ENNReal.ofReal (quantumEventProbability F (fun k => (ell k)⁻¹) A))⁻¹ •
            Measure.map Prod.fst
              (((graphRawLaw F).prod
                (Measure.pi (fun _ : Fin K × (Fin N × Fin 3) => compactNoiseLaw))).restrict
                  (quantumObservationEvent (fun k => (ell k)⁻¹) A)) ∧
        formEnergy Z (graphFormVector G) ≤ energy Z N +
          (observationFisherConstant/2) * (∑ k, ((ell k)⁻¹)^2) *
            (Real.log (Real.exp 1/quantumEventProbability F (fun k => (ell k)⁻¹) A))^5 + δ)
  · intro F h
    refine ⟨h.1,h.2.1,fun A hA hsy hp => ?_⟩
    have hm := hA.preimage (scaleObservationArray ell).measurable
    have hp' : p₀ ≤ quantumEventProbability F (fun k => (ell k)⁻¹)
        (scaleObservationArray ell ⁻¹' A) := by
      rwa [quantumEventProbability_eq_physical F h.1 ell hell hA]
    obtain ⟨G,hG,hlaw,hcost⟩ := h.2.2 (scaleObservationArray ell ⁻¹' A) hm
      (scaledObservationEvent_symmetric ell hsy) hp'
    rw [quantumEventProbability_eq_physical F h.1 ell hell hA,
      physicalObservationEvent_eq ell hell] at hlaw
    rw [quantumEventProbability_eq_physical F h.1 ell hell hA] at hcost
    exact ⟨G,hG,hlaw,hcost⟩
  · exact quantum_uniform_near_minimizer_event_tilt hZ N (fun k => (ell k)⁻¹) h₀ hδ

end CoulombAtom

end

end OAI
