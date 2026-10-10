import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SelectedMasterComparison

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

def observationTiltEnergyCost {K : ℕ} (ell : Fin K → ℝ) (p : ℝ) : ℝ :=
  (observationFisherConstant/2)*(∑ k, ((ell k)⁻¹)^2)*(Real.log (Real.exp 1/p))^5

lemma priced_graph_tilt_excess {Z lam e : ℝ} {N : ℕ}
    (hN : PriceMinimizes (energy Z) lam N) (G : fermionGraph N)
    (hn : ‖fermionGraphValue N G‖^2 = 1)
    (hE : formEnergy Z (graphFormVector G) ≤ energy Z N+e) :
    corePriceExcess Z lam (graphFormVector G) ≤ e := by
  rw [corePriceExcess,formMass_graph,hn,mul_one,mul_one,priceEnergy_eq_of_minimizes hN]
  linarith

theorem quantum_priced_event_selected_master_center {Z lam : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) {N K : ℕ} (hN : PriceMinimizes (energy Z) lam N)
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
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : 7*b < 5*a) (hy : 6*a+2*b ≤ ‖y‖)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(5*a-4*b)/4) :
    ∃ G : fermionGraph N,
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell A))⁻¹ •
        Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
          (physicalObservationEvent ell A)) ∧
      corePriceExcess Z lam (graphFormVector G) ≤
        observationTiltEnergyCost ell (physicalObservationProbability F ell A) ∧
      ∃ t ∈ Icc (5*a) (6*a), ∃ ht : 0 ≤ t,
      |Z/‖y‖-lam-(physicalObservationProbability F ell A)⁻¹*
        (∫ z in physicalObservationEvent ell A,
          tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g (originalDatum ell j z)) y
          ∂physicalObservationLaw (graphRawLaw F) K)-
        expectedRadialPatchCenter (graphFormVector G) y ht hb Z lam| ≤
        selectedPotentialError (graphFormVector G) y a ht hb Z lam q g+
        (∫ x, rawLocalPotential y (2*masterWidth c₁ r₀ s y) x ∂graphRawLaw G) := by
  obtain ⟨G,hG,hlaw,hE,ht⟩ := quantum_event_selected_master_center hZ F hn hF ell hell j
    hA hsy hinfo hp y hc hcL hr hs hs1 hg hcg hgn hrad hgs ha hb hba hy hlam hq hqR
  exact ⟨G,hG,hlaw,priced_graph_tilt_excess hN G hG hE,ht⟩

end CoulombAtom

end

end OAI
