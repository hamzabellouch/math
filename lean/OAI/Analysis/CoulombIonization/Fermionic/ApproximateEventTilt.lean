import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.QuantumEventTilt
import OAI.Analysis.CoulombIonization.FormDomain.ApproximateLipschitz

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

namespace CoulombAtom
open CoulombObservation

attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator

lemma quantum_lipschitz_ims_residual {N : ℕ} (Z : ℝ) (F : fermionGraph N)
    (p : FermionLipschitzMultiplier N) :
    formEnergy Z (graphFormVector (p.apply F)) -
      energy Z N * ‖fermionGraphValue N (p.apply F)‖^2 =
      (1/2:ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ∫ x, (lineDeriv ℝ p.value x (direction i a))^2 *
          ‖graphComponent s none F x‖^2) +
        (⟪p.apply (p.apply F), sectorExcessOperator Z N F⟫_ℂ).re := by
  have hi := FermionLipschitzMultiplier.form_ims (N := N) p Z F
  have hr := sectorExcessOperator_pair Z (p.apply (p.apply F)) F
  have hr' := hr.trans (congrArg (fun u : ℝ =>
    (⟪p.apply (p.apply F),coulombFormOperator Z N F⟫_ℂ).re-energy Z N*u)
    (FermionLipschitzMultiplier.value_pairing (N := N) p F))
  linarith only [hr',hi]

lemma quantum_lipschitz_residual_estimate {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    {η : ℝ} (hη : 0 ≤ η)
    (hF : formEnergy Z (graphFormVector F) ≤ energy Z N + η)
    (p : FermionLipschitzMultiplier N) :
    (⟪p.apply (p.apply F), sectorExcessOperator Z N F⟫_ℂ).re ≤
      Real.sqrt (η * (‖sectorExcessOperator Z N‖ * ‖p.apply (p.apply F)‖^2)) := by
  have hex : (⟪F,sectorExcessOperator Z N F⟫_ℂ).re ≤ η := by
    have he := sectorExcessOperator_diagonal Z F
    have hev : energy Z N * ‖fermionGraphValue N F‖^2 = energy Z N :=
      (congrArg (fun t : ℝ => energy Z N*t) hn).trans (mul_one _)
    exact he.le.trans ((sub_le_sub_left hev.ge _).trans
      (sub_le_iff_le_add.mpr (by linarith only [hF])))
  have hr := positive_form_residual_bound (sectorExcessOperator Z N)
    (sectorExcessOperator_positive hZ N) F (p.apply (p.apply F)) hη hex
    (C := ‖p.apply (p.apply F)‖^2) (K := 1) (le_of_eq (mul_one _).symm)
  have hr' := hr.trans_eq (congrArg (fun u : ℝ => η*u) (mul_one _))
  have hnR : 0 ≤ η * (‖sectorExcessOperator Z N‖ * ‖p.apply (p.apply F)‖^2) := by positivity
  have hs := Real.sq_sqrt hnR
  have hsn := Real.sqrt_nonneg (η * (‖sectorExcessOperator Z N‖ * ‖p.apply (p.apply F)‖^2))
  nlinarith only [hr',hs,hsn]

lemma FermionLipschitzMultiplier.double_graph_bound {N : ℕ}
    (p : FermionLipschitzMultiplier N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : fermionGraph N, ‖p.apply (p.apply F)‖^2 ≤ C*‖F‖^2 := by
  obtain ⟨C,hC,hp⟩ := FermionLipschitzMultiplier.graph_bound (N := N) p
  refine ⟨C*C,mul_nonneg hC hC,fun F => ?_⟩
  exact (hp (p.apply F)).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hp F) hC)

lemma quantum_approximate_double_lipschitz {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    (p : FermionLipschitzMultiplier N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      (⟪p.apply (p.apply F),sectorExcessOperator Z N F⟫_ℂ).re ≤ δ := by
  exact approximate_positive_form (sectorExcessOperator Z N)
    (sectorExcessOperator_positive hZ N) (fun F => p.apply (p.apply F))
    (FermionLipschitzMultiplier.double_graph_bound (N := N) p)
    (fun F => ‖fermionGraphValue N F‖^2 = 1) (by positivity)
    (fun _ hη => quantum_sector_excess_near_minimizer hZ N hη) hδ

theorem quantum_near_minimizer_lipschitz_ims {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    (p : FermionLipschitzMultiplier N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      formEnergy Z (graphFormVector (p.apply F)) ≤
        energy Z N * ‖fermionGraphValue N (p.apply F)‖^2 +
        (1/2:ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
          ∫ x, (lineDeriv ℝ p.value x (direction i a))^2 *
            ‖graphComponent s none F x‖^2) + δ := by
  apply Exists.imp (p := fun F : fermionGraph N =>
      ‖fermionGraphValue N F‖^2 = 1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      (⟪p.apply (p.apply F),sectorExcessOperator Z N F⟫_ℂ).re ≤ δ)
  · intro F h
    refine ⟨h.1,h.2.1,?_⟩
    have hi := quantum_lipschitz_ims_residual Z F p
    have hr := h.2.2
    linarith only [hi,hr]
  · exact quantum_approximate_double_lipschitz hZ N p hδ

theorem quantum_observation_event_tilt_near_minimizer {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    {η : ℝ} (hη : 0 ≤ η)
    (hF : formEnergy Z (graphFormVector F) ≤ energy Z N + η)
    {J : Type*} [Fintype J] (b : J → ℝ)
    {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (hp : 0 < quantumEventProbability F b s) :
    let p := quantumEventMultiplier b hs hsy (quantumEventProbability F b s)
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
          (Real.log (Real.exp 1/quantumEventProbability F b s))^5 +
        Real.sqrt (η * (‖sectorExcessOperator Z N‖ * ‖p.apply (p.apply F)‖^2)) := by
  let p := quantumEventMultiplier b hs hsy (quantumEventProbability F b s)
  refine ⟨p.apply F,quantumEventMultiplier_normalized F b hs hsy hp,
    quantumEventMultiplier_rawLaw F b hs hsy hp,?_⟩
  have hid := quantum_lipschitz_ims_residual Z F p
  have hnorm : energy Z N * ‖fermionGraphValue N (p.apply F)‖^2 = energy Z N :=
    (congrArg (fun u : ℝ => energy Z N*u)
      (quantumEventMultiplier_normalized F b hs hsy hp)).trans (mul_one _)
  have hgrad := FermionLipschitzMultiplier.gradient_rawLaw (N := N) p F
  have hc := quantumEventMultiplier_fisher_integral F hn b hs hsy hp
  have hr := quantum_lipschitz_residual_estimate hZ F hn hη hF p
  change formEnergy Z (graphFormVector (p.apply F)) ≤ _
  linarith only [hid,hnorm,hgrad,hc,hr]

end CoulombAtom

end

end OAI
