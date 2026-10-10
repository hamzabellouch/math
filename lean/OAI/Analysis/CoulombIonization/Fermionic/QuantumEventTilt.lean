import Mathlib
import OAI.Analysis.CoulombIonization.Localization.QuantumMultiplierLaw

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom
open CoulombObservation

lemma quantumEventMultiplier_normalized {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)}
    (hs : MeasurableSet s) (hsy : QuantumEventSymmetric s)
    (hp : 0 < quantumEventProbability F b s) :
    ‖fermionGraphValue N
      ((quantumEventMultiplier b hs hsy (quantumEventProbability F b s)).apply F)‖^2 = 1 := by
  rw [FermionLipschitzMultiplier.apply_norm_sq]
  simp only [quantumEventMultiplier_sq b hs hsy hp]
  rw [integral_const_mul]
  exact inv_mul_cancel₀ hp.ne'

theorem quantum_observation_event_tilt {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    (hF : formEnergy Z (graphFormVector F) = energy Z N)
    {J : Type*} [Fintype J] (b : J → ℝ)
    {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (hp : 0 < quantumEventProbability F b s) :
    ∃ G : fermionGraph N,
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G =
        (ENNReal.ofReal (quantumEventProbability F b s))⁻¹ •
          Measure.map Prod.fst
            (((graphRawLaw F).prod
              (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw))).restrict
                (quantumObservationEvent b s)) ∧
      formEnergy Z (graphFormVector G) ≤ energy Z N +
        (observationFisherConstant/2) * (∑ j, (b j)^2) *
          (Real.log (Real.exp 1/quantumEventProbability F b s))^5 := by
  let m := quantumEventMultiplier b hs hsy (quantumEventProbability F b s)
  refine ⟨m.apply F, quantumEventMultiplier_normalized F b hs hsy hp,
    quantumEventMultiplier_rawLaw F b hs hsy hp, ?_⟩
  have hid := quantum_ground_multiplier_lipschitz hZ F hn hF m
  rw [quantumEventMultiplier_normalized F b hs hsy hp, mul_one,
    FermionLipschitzMultiplier.gradient_rawLaw] at hid
  have hc := quantumEventMultiplier_fisher_integral F hn b hs hsy hp
  change formEnergy Z (graphFormVector (m.apply F)) ≤ _
  linarith

end CoulombAtom

end

end OAI
