import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SelectedMasterComparison
import OAI.Analysis.CoulombIonization.Localization.OrdinaryDensity

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

theorem eventLaw_selected_master_density {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {N K : ℕ} (F G : fermionGraph N) (hG : ‖fermionGraphValue N G‖^2 = 1)
    (ell : Fin K → ℝ) (j : ℕ) {A : Set (Fin K × (Fin N × Fin 3) → ℝ)}
    (hinfo : MeasurableSet[observationInformation ell j] (physicalObservationEvent ell A))
    (hp : 0 < physicalObservationProbability F ell A)
    (hlaw : graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell A))⁻¹ •
      Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
        (physicalObservationEvent ell A)))
    (y : Space) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : 7*b < 5*a) (hy : 6*a+2*b ≤ ‖y‖)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(5*a-4*b)/4) :
    ∃ t ∈ Icc (5*a) (6*a), ∃ ht : 0 ≤ t,
      |Z/‖y‖-lam-(physicalObservationProbability F ell A)⁻¹*
        (∫ z in physicalObservationEvent ell A,
          tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g (originalDatum ell j z)) y
          ∂physicalObservationLaw (graphRawLaw F) K)-
        expectedRadialPatchCenter (graphFormVector G) y ht hb Z lam| ≤
        selectedPotentialError (graphFormVector G) y a ht hb Z lam q g+
        (∫ z in ball y (2*masterWidth c₁ r₀ s y),
          ordinaryDensity (graphFormVector G) z/‖z-y‖) := by
  have hmass : formMass (graphFormVector G) = 1 := (formMass_graph G).trans hG
  obtain ⟨t,ht,ht0,herr⟩ := exists_selected_radial_potential_error
    (graphFormVector_sobolev G) hmass y ha hb hba hy hZ hlam hg hcg hgn hrad hgs hq
  refine ⟨t,ht,ht0,?_⟩
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    rw [←formRawLaw_graph]
    exact rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    rw [←formRawLaw_graph]
    exact formRawLaw_ae_no_poles (graphFormVector F) y
  have hh := original_master_radial_center_comparison (graphRawLaw F) (graphFormVector_sobolev G)
    ell j y hi he hc hcL hr hs hs1 hg hcg hgn hrad hgs hinfo hp
    (by rw [formRawLaw_graph]; exact hlaw) ht0 hb (by linarith [ht.1])
    (by linarith [ht.2]) hZ hlam hq (by linarith [ht.1])
  have hh' := hh.trans (add_le_add herr le_rfl)
  have hd := ordinaryDensity_raw_local_potential
    (graphFormVector_sobolev G).sobolevVector y (2*masterWidth c₁ r₀ s y)
  simpa only [hmass,mul_one,hd] using hh'

end CoulombAtom

end

end OAI
