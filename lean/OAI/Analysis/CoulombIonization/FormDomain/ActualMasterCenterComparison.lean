import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.NormalizedMasterEvent

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma graphFormVector_sobolev {N : ℕ} (F : fermionGraph N) :
    SobolevFermion (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_⟩
  · intro s i a
    exact (mem_weakGraph _ _).mp (F.val s).property (i,a)
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s

instance graphRawLaw_finite {N : ℕ} (F : fermionGraph N) : IsFiniteMeasure (graphRawLaw F) := by
  constructor
  rw [graphRawLaw_univ]
  exact ENNReal.ofReal_lt_top

lemma formRawLaw_graph {N : ℕ} (F : fermionGraph N) :
    formRawLaw (graphFormVector F) = graphRawLaw F := rfl

lemma formMass_graph {N : ℕ} (F : fermionGraph N) :
    formMass (graphFormVector F) = ‖fermionGraphValue N F‖^2 := by
  rw [←formRawDensity_integral (graphFormVector_sobolev F).sobolevVector]
  exact graphRawDensity_integral F

theorem quantum_event_original_master_center {Z : ℝ} (hZ : 0 ≤ Z) {N K : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    (hF : formEnergy Z (graphFormVector F) = energy Z N)
    (ell : Fin K → ℝ) (hell : ∀ k, 0 < ell k) (j : ℕ)
    {A : Set (Fin K × (Fin N × Fin 3) → ℝ)} (hA : MeasurableSet A)
    (hsy : QuantumEventSymmetric A)
    (hinfo : MeasurableSet[observationInformation ell j] (physicalObservationEvent ell A))
    (hp : 0 < physicalObservationProbability F ell A)
    (y : Space) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (htb : 7*b < t) (hy : t ≤ ‖y‖)
    {lam q : ℝ} (hlam : 0 < lam) (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    ∃ G : fermionGraph N,
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell A))⁻¹ •
        Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
          (physicalObservationEvent ell A)) ∧
      formEnergy Z (graphFormVector G) ≤ energy Z N+
        (observationFisherConstant/2)*(∑ k, ((ell k)⁻¹)^2)*
          (Real.log (Real.exp 1/physicalObservationProbability F ell A))^5 ∧
      |Z/‖y‖-lam-(physicalObservationProbability F ell A)⁻¹*
        (∫ z in physicalObservationEvent ell A,
          tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g (originalDatum ell j z)) y
          ∂physicalObservationLaw (graphRawLaw F) K)-
        expectedRadialPatchCenter (graphFormVector G) y ht hb Z lam| ≤
        radialPotentialError (graphFormVector G) y ht hb Z lam q+
        (∫ x, rawLocalPotential y (2*masterWidth c₁ r₀ s y) x ∂graphRawLaw G) := by
  obtain ⟨G,hG,hlaw,hE⟩ := quantum_physical_observation_event_tilt hZ F hn hF ell hell hA hsy hp
  refine ⟨G,hG,hlaw,hE,?_⟩
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    rw [←formRawLaw_graph]
    exact rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    rw [←formRawLaw_graph]
    exact formRawLaw_ae_no_poles (graphFormVector F) y
  have hh := original_master_radial_center_comparison (graphRawLaw F) (graphFormVector_sobolev G)
    ell j y hi he hc hcL hr hs hs1 hg hcg hgn hrad hgs hinfo hp
    (by rw [formRawLaw_graph]; exact hlaw) ht hb htb hy hZ hlam hq hqR
  simpa only [formMass_graph,hG,mul_one,formRawLaw_graph] using hh

end CoulombAtom

end

end OAI
