import Mathlib
import OAI.Analysis.CoulombIonization.Variational.ActualSectorPlateau
import OAI.Analysis.CoulombIonization.Localization.UniformDyadicEvent

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector
  fermionGraph weakGraph fermionGraphValue formEnergy energy corePriceExcess

lemma actual_priced_sector_unshifted_bound (Z : ℕ) {lam : ℝ}
    {N : ℕ} (hN : PriceMinimizes (energy Z) lam N) :
    energy Z N ≤ sInf (Set.range (energy (Z:ℝ)))+lam*(2*(Z:ℝ)+1-(N:ℝ)) := by
  have hh := hN (2*Z+1)
  rw [quantum_unpriced_infimum_finite]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hh
  nlinarith only [hh]

lemma actual_priced_excess_unshifted_bound (Z : ℕ) {lam : ℝ} (hlam : 0 < lam)
    {N : ℕ} (G : fermionGraph N) (hn : ‖fermionGraphValue N G‖^2 = 1)
    {e : ℝ} (he : corePriceExcess Z lam (graphFormVector G) ≤ e) :
    formEnergy Z (graphFormVector G) ≤ sInf (Set.range (energy (Z:ℝ)))+
      lam*(2*(Z:ℝ)+1-(N:ℝ))+e := by
  have hp := quantum_price_le_sector (Nat.cast_nonneg Z) hlam (2*Z+1)
  rw [quantum_unpriced_infimum_finite]
  rw [corePriceExcess,formMass_graph,hn,mul_one,mul_one] at he
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hp
  nlinarith only [he,hp]

theorem actual_priced_uniform_unshifted_event_tilt (Z : ℕ) (hZ : 1 ≤ Z)
    {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) {N : ℕ}
    (hN : PriceMinimizes (energy Z) lam N) (K : ℕ) {p₀ δ : ℝ}
    (h₀ : 0 < p₀) (hδ : 0 < δ) :
    N ≤ 3*Z ∧
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
        formEnergy Z (graphFormVector G) ≤ sInf (Set.range (energy (Z:ℝ)))+3*Z*lam+
          observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/
            physicalObservationProbability F (fun k : Fin K => dyadicObservationWidth r k) A))^5+δ := by
  refine ⟨actual_priced_particle_bound_three Z hZ hlam hN,?_⟩
  have he : energy Z N ≤ sInf (Set.range (energy (Z:ℝ)))+3*Z*lam := by
    have hh := actual_priced_sector_unshifted_bound Z hN
    have hz : (1:ℝ) ≤ Z := by exact_mod_cast hZ
    have hnon : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    have hb : 2*(Z:ℝ)+1-(N:ℝ) ≤ 3*Z := by linarith only [hz,hnon]
    have hm := mul_le_mul_of_nonneg_left hb hlam.le
    nlinarith only [hh,hm]
  apply Exists.imp (p := fun F : fermionGraph N =>
      ‖fermionGraphValue N F‖^2 = 1 ∧
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
            physicalObservationProbability F (fun k : Fin K => dyadicObservationWidth r k) A))^5+δ)
  · intro F h
    refine ⟨h.1,h.2.1,fun A hA hsy hp => ?_⟩
    obtain ⟨G,hn,hlaw,hE⟩ := h.2.2 A hA hsy hp
    refine ⟨G,hn,hlaw,?_⟩
    linarith only [hE,he]
  · exact quantum_uniform_near_minimizer_dyadic_event_tilt (Nat.cast_nonneg Z) hr N K h₀ hδ

end CoulombAtom

end

end OAI
