import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.ApproximateEventTilt
import OAI.Analysis.CoulombIonization.Localization.UniformEventGraph
import OAI.Analysis.CoulombIonization.FormDomain.UniformFormResidual

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace NNReal

namespace CoulombAtom
open CoulombObservation

attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator quantumEventMultiplier

lemma quantum_observation_event_tilt_bounded_residual {Z δ : ℝ} {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    {J : Type*} [Fintype J] (b : J → ℝ)
    {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (hp : 0 < quantumEventProbability F b s)
    (hr : let p := quantumEventMultiplier b hs hsy (quantumEventProbability F b s)
      (⟪p.apply (p.apply F),sectorExcessOperator Z N F⟫_ℂ).re ≤ δ) :
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
          (Real.log (Real.exp 1/quantumEventProbability F b s))^5 + δ := by
  let p := quantumEventMultiplier b hs hsy (quantumEventProbability F b s)
  refine ⟨p.apply F,quantumEventMultiplier_normalized F b hs hsy hp,
    quantumEventMultiplier_rawLaw F b hs hsy hp,?_⟩
  have hid := quantum_lipschitz_ims_residual Z F p
  have hnorm : energy Z N * ‖fermionGraphValue N (p.apply F)‖^2 = energy Z N :=
    (congrArg (fun u : ℝ => energy Z N*u)
      (quantumEventMultiplier_normalized F b hs hsy hp)).trans (mul_one _)
  have hgrad := FermionLipschitzMultiplier.gradient_rawLaw (N := N) p F
  have hc := quantumEventMultiplier_fisher_integral F hn b hs hsy hp
  change formEnergy Z (graphFormVector (p.apply F)) ≤ _
  linarith only [hid,hnorm,hgrad,hc,hr]

theorem quantum_uniform_near_minimizer_event_tilt {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    {J : Type*} [Fintype J] (b : J → ℝ) {p₀ δ : ℝ} (h₀ : 0 < p₀) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (s : Set (J × (Fin N × Fin 3) → ℝ)) (_hs : MeasurableSet s)
        (_hsy : QuantumEventSymmetric s), p₀ ≤ quantumEventProbability F b s →
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
            (Real.log (Real.exp 1/quantumEventProbability F b s))^5 + δ := by
  let C : ℝ := observationGraphFactor N b p₀
  let K : ℝ := 4*(|energy Z N|+(N:ℝ)*Z^2+2)
  let H : ℝ := C*C*K
  have hC : 0 ≤ C := observationGraphFactor_nonneg N b p₀
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg hC hC) hK
  apply Exists.imp (p := fun F : fermionGraph N =>
      ‖fermionGraphValue N F‖^2 = 1 ∧ ‖F‖^2 ≤ K ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ G : fermionGraph N, ‖G‖^2 ≤ H →
        (⟪G,sectorExcessOperator Z N F⟫_ℂ).re ≤ δ)
  · intro F h
    refine ⟨h.1,h.2.2.1,fun s hs hsy hp => ?_⟩
    let p := quantumEventMultiplier b hs hsy (quantumEventProbability F b s)
    have hb (G : fermionGraph N) : ‖p.apply G‖^2 ≤ C*‖G‖^2 :=
      quantumEventMultiplier_uniform_graph b hs hsy h₀ hp G
    have htest : ‖p.apply (p.apply F)‖^2 ≤ H := calc
      _ ≤ C*‖p.apply F‖^2 := hb (p.apply F)
      _ ≤ C*(C*‖F‖^2) := mul_le_mul_of_nonneg_left (hb F) hC
      _ ≤ C*(C*K) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h.2.1 hC) hC
      _ = H := by dsimp only [H]; ring
    exact quantum_observation_event_tilt_bounded_residual F h.1 b hs hsy (h₀.trans_le hp)
      (h.2.2.2 (p.apply (p.apply F)) htest)
  · exact quantum_uniform_form_residual hZ N hH hδ

end CoulombAtom

end

end OAI
