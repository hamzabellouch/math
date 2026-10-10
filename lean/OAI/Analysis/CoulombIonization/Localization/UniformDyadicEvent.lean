import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.UniformPhysicalEvent

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

lemma physicalObservationProbability_le_one {N K : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) (ell : Fin K → ℝ)
    (A : Set (Fin K × (Fin N × Fin 3) → ℝ)) :
    physicalObservationProbability F ell A ≤ 1 := by
  let := graphRawLaw_probability F hn
  exact measureReal_le_one

lemma observationTiltEnergyCost_dyadic {r p : ℝ} (hr : 0 < r) (hp : 0 < p)
    (hp1 : p ≤ 1) (K : ℕ) :
    observationTiltEnergyCost (fun k : Fin K => dyadicObservationWidth r k) p ≤
      observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/p))^5 := by
  have hlog : 0 ≤ (Real.log (Real.exp 1/p))^5 := by
    apply pow_nonneg
    rw [eventLog_eq hp]
    linarith [Real.log_nonpos hp.le hp1]
  have hsum := dyadicObservation_inv_sq_sum hr K
  have hC := observationFisherConstant_pos
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum (show 0 ≤ observationFisherConstant/2 by positivity)) hlog
  unfold observationTiltEnergyCost
  exact hh.trans_eq (by ring)

theorem quantum_uniform_near_minimizer_dyadic_event_tilt {Z r : ℝ} (hZ : 0 ≤ Z)
    (hr : 0 < r) (N K : ℕ) {p₀ δ : ℝ} (h₀ : 0 < p₀) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (A : Set (Fin K × (Fin N × Fin 3) → ℝ)) (_hA : MeasurableSet A)
        (_hsy : QuantumEventSymmetric A),
        p₀ ≤ physicalObservationProbability F (fun k : Fin K => dyadicObservationWidth r k) A →
      ∃ G : fermionGraph N,
        ‖fermionGraphValue N G‖^2 = 1 ∧
        graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F
          (fun k : Fin K => dyadicObservationWidth r k) A))⁻¹ •
          Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
            (physicalObservationEvent (fun k : Fin K => dyadicObservationWidth r k) A)) ∧
        formEnergy Z (graphFormVector G) ≤ energy Z N+
          observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/
            physicalObservationProbability F (fun k : Fin K => dyadicObservationWidth r k) A))^5+δ := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  apply Exists.imp (p := fun F : fermionGraph N =>
      ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (A : Set (Fin K × (Fin N × Fin 3) → ℝ)) (_hA : MeasurableSet A)
        (_hsy : QuantumEventSymmetric A), p₀ ≤ physicalObservationProbability F ell A →
      ∃ G : fermionGraph N,
        ‖fermionGraphValue N G‖^2 = 1 ∧
        graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell A))⁻¹ •
          Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
            (physicalObservationEvent ell A)) ∧
        formEnergy Z (graphFormVector G) ≤ energy Z N+
          observationTiltEnergyCost ell (physicalObservationProbability F ell A)+δ)
  · intro F h
    refine ⟨h.1,h.2.1,fun A hA hsy hp => ?_⟩
    apply Exists.imp (p := fun G : fermionGraph N =>
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell A))⁻¹ •
        Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
          (physicalObservationEvent ell A)) ∧
      formEnergy Z (graphFormVector G) ≤ energy Z N+
        observationTiltEnergyCost ell (physicalObservationProbability F ell A)+δ)
    · intro G hG
      refine ⟨hG.1,hG.2.1,hG.2.2.trans ?_⟩
      exact add_le_add_left (add_le_add_right
        (observationTiltEnergyCost_dyadic hr (h₀.trans_le hp)
          (physicalObservationProbability_le_one F h.1 ell A) K) _) _
    · exact h.2.2 A hA hsy hp
  · exact quantum_uniform_near_minimizer_physical_event_tilt hZ N K ell
      (fun k => dyadicObservationWidth_pos hr k) h₀ hδ

end CoulombAtom

end

end OAI
