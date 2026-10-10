import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ActualPosteriorCapBarrier
import OAI.Analysis.CoulombIonization.ThomasFermi.UniformVariableTailEventBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

def TailTiltState {N : ℕ} (Z lam r : ℝ) (K : ℕ) (p₀ : Fin (K+1) → ℝ) (δ : ℝ)
    (F : fermionGraph N) : Prop :=
  ‖fermionGraphValue N F‖^2 = 1 ∧
    formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
    ∀ (j : Fin (K+1))
      (A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)))
      (_hA : MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j] A),
      p₀ j ≤ ((physicalObservationLaw (graphRawLaw F) K) A).toReal →
    ∃ G : fermionGraph N,
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G = (ENNReal.ofReal (((physicalObservationLaw (graphRawLaw F) K) A).toReal))⁻¹ •
        Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict A) ∧
      max (corePriceExcess Z lam (graphFormVector G)) 0 ≤
        dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ

theorem exists_actual_tail_tilt_state {Z lam r : ℝ} (hZ : 0 ≤ Z) (hr : 0 < r)
    {N : ℕ} (hN : PriceMinimizes (energy Z) lam N) (K : ℕ)
    (p₀ : Fin (K+1) → ℝ) {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (h₀1 : ∀ j, p₀ j ≤ 1) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, TailTiltState Z lam r K p₀ δ F := by
  obtain ⟨F,hFn,hFE,hTilt⟩ := quantum_uniform_near_minimizer_variable_tail_event_tilt hZ hr N K p₀ h₀ hδ
  refine ⟨F,hFn,hFE,?_⟩
  intro j A hA hp
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  obtain ⟨B,hB,hBA⟩ := observation_event_tail_representation ell j hA
  have hpB : physicalObservationProbability F ell B =
      ((physicalObservationLaw (graphRawLaw F) K) A).toReal := by
    change ((physicalObservationLaw (graphRawLaw F) K) (physicalObservationEvent ell B)).toReal = _
    rw [hBA]
  have hp' : p₀ j ≤ physicalObservationProbability F ell B := by rwa [hpB]
  obtain ⟨G,hGn,hlaw,hGE⟩ := hTilt j B hB hp'
  refine ⟨G,hGn,?_,?_⟩
  · rwa [hpB,hBA] at hlaw
  · have hrj : 0 < (2:ℝ)^j.val*r := by positivity
    apply max_le _ (dyadicUniformEventBudget_nonneg hrj (h₀ j) (h₀1 j) hδ.le)
    apply (priced_graph_tilt_excess hN G hGn (by simpa only [add_assoc] using hGE)).trans
    exact dyadicUniformEventBudget_mono hrj (h₀ j) hp'
      (physicalObservationProbability_le_one F hFn ell B)
end CoulombAtom

end

end OAI
