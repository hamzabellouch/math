import Mathlib
import OAI.Analysis.CoulombIonization.Localization.UniformApproximateEvent

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UniformFamilyEvent_barrier_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace NNReal

open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator quantumEventMultiplier

theorem quantum_uniform_near_minimizer_family_event_tilt {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    {I J : Type*} [Fintype I] [Fintype J] (b : I → J → ℝ)
    {p₀ δ : ℝ} (h₀ : 0 < p₀) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (i : I) (s : Set (J × (Fin N × Fin 3) → ℝ)) (_hs : MeasurableSet s)
        (_hsy : QuantumEventSymmetric s), p₀ ≤ quantumEventProbability F (b i) s →
      ∃ G : fermionGraph N,
        ‖fermionGraphValue N G‖^2 = 1 ∧
        graphRawLaw G = (ENNReal.ofReal (quantumEventProbability F (b i) s))⁻¹ •
          Measure.map Prod.fst
            (((graphRawLaw F).prod
              (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw))).restrict
                (quantumObservationEvent (b i) s)) ∧
        formEnergy Z (graphFormVector G) ≤ energy Z N +
          (observationFisherConstant/2) * (∑ j, (b i j)^2) *
            (Real.log (Real.exp 1/quantumEventProbability F (b i) s))^5 + δ := by
  classical
  let C : ℝ := ∑ i, observationGraphFactor N (b i) p₀
  let K : ℝ := 4*(|energy Z N|+(N:ℝ)*Z^2+2)
  let H : ℝ := C*C*K
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => observationGraphFactor_nonneg N (b i) p₀)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg hC hC) hK
  have hi (i : I) : observationGraphFactor N (b i) p₀ ≤ C :=
    Finset.single_le_sum (fun k _ => observationGraphFactor_nonneg N (b k) p₀) (Finset.mem_univ i)
  apply Exists.imp (p := fun F : fermionGraph N =>
      ‖fermionGraphValue N F‖^2 = 1 ∧ ‖F‖^2 ≤ K ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ G : fermionGraph N, ‖G‖^2 ≤ H →
        (⟪G,sectorExcessOperator Z N F⟫_ℂ).re ≤ δ)
  · intro F h
    refine ⟨h.1,h.2.2.1,fun i s hs hsy hp => ?_⟩
    let p := quantumEventMultiplier (b i) hs hsy (quantumEventProbability F (b i) s)
    have hb (G : fermionGraph N) : ‖p.apply G‖^2 ≤ C*‖G‖^2 :=
      (quantumEventMultiplier_uniform_graph (b i) hs hsy h₀ hp G).trans
        (mul_le_mul_of_nonneg_right (hi i) (sq_nonneg _))
    have htest : ‖p.apply (p.apply F)‖^2 ≤ H := calc
      _ ≤ C*‖p.apply F‖^2 := hb (p.apply F)
      _ ≤ C*(C*‖F‖^2) := mul_le_mul_of_nonneg_left (hb F) hC
      _ ≤ C*(C*K) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h.2.1 hC) hC
      _ = H := by dsimp only [H]; ring
    exact quantum_observation_event_tilt_bounded_residual F h.1 (b i) hs hsy (h₀.trans_le hp)
      (h.2.2.2 (p.apply (p.apply F)) htest)
  · exact quantum_uniform_form_residual hZ N hH hδ

end Work_UniformFamilyEvent_barrier_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace NNReal

open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator quantumEventMultiplier

theorem quantum_uniform_near_minimizer_family_variable_event_tilt {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] (b : I → J → ℝ)
    (p₀ : I → ℝ) {δ : ℝ} (h₀ : ∀ i, 0 < p₀ i) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (i : I) (s : Set (J × (Fin N × Fin 3) → ℝ)) (_hs : MeasurableSet s)
        (_hsy : QuantumEventSymmetric s), p₀ i ≤ quantumEventProbability F (b i) s →
      ∃ G : fermionGraph N,
        ‖fermionGraphValue N G‖^2 = 1 ∧
        graphRawLaw G = (ENNReal.ofReal (quantumEventProbability F (b i) s))⁻¹ •
          Measure.map Prod.fst
            (((graphRawLaw F).prod
              (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw))).restrict
                (quantumObservationEvent (b i) s)) ∧
        formEnergy Z (graphFormVector G) ≤ energy Z N +
          (observationFisherConstant/2) * (∑ j, (b i j)^2) *
            (Real.log (Real.exp 1/quantumEventProbability F (b i) s))^5 + δ := by
  classical
  let p := Finset.univ.inf' Finset.univ_nonempty p₀
  have hp : 0 < p := (Finset.lt_inf'_iff _).mpr (fun i _ => h₀ i)
  have hle (i : I) : p ≤ p₀ i := Finset.inf'_le p₀ (Finset.mem_univ i)
  obtain ⟨F,hFn,hFE,hTilt⟩ := quantum_uniform_near_minimizer_family_event_tilt hZ N b hp hδ
  exact ⟨F,hFn,hFE,fun i s hs hsy hp => hTilt i s hs hsy ((hle i).trans hp)⟩

end CoulombAtom

end

end OAI
