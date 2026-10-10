import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SelectedPatchBudget
import OAI.Analysis.CoulombIonization.FormDomain.ActualMasterCenterComparison

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann CoulombObservation

theorem selected_fresh_patch_budget_with_deletion {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hba : 7*b < 5*a) (hy : 6*a+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    ∃ t ∈ Icc (5*a) (6*a), ∃ ht : 0 ≤ t,
      let p := coreFirstRadialCut y ht hb
      let hp := coreFirstRadialCut_partition y ht hb
      let B := ∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ
      (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        (outerDeletedCount y t b u)^2*
          formMass (coreSlice (orderedCutForm p hp ψ c) s u)) ≤ (8*b/a)*B ∧
      (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchGap (orderedCutForm p hp ψ c) s Z lam y (t-4*b) hb
          (radialPatchRetention L y t b c s) u) ≤
        corePriceExcess Z lam ψ+
        (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2*((8*b/a)*B)^(1/2:ℝ)+
        b⁻¹^2*neumannRemainderConstant*(B^(2/3:ℝ)+B^(1/2:ℝ))+
        (((2*Real.pi+1)/2)/b)*B^(1/2:ℝ)+
        Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*Real.sqrt ((8*b/a)*B)+
        ((packetDirichlet g/2)*b⁻¹^2)*freshPatchMass p hp ψ Z lam y (t-4*b) := by
  obtain ⟨t,ht,ht0,hd,hfirst,h43,hims⟩ :=
    radial_fresh_selected_counts hψ.sobolevVector hm y ha hb (by linarith)
  refine ⟨t,ht,ht0,hd,?_⟩
  have htb : 7*b < t := lt_of_lt_of_le hba ht.1
  have hty : t+2*b ≤ ‖y‖ := le_trans (by linarith [ht.2]) hy
  have he := radial_fresh_patch_budget hψ y hb htb (by linarith) hZ hlam hg hcg hgn hr hgs
  dsimp only at he ⊢
  rw [radial_fresh_tail_split hψ.sobolevVector y _ hb (by linarith) (by linarith)] at he
  have hdel := radial_deleted_field_budget hψ.sobolevVector y ht0 hb hty hZ hlam.le
  dsimp only at hdel
  have hds := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd)
    (Real.sqrt_nonneg (freshOutMaximumSecondMoment (coreFirstRadialCut y ht0 hb) (coreFirstRadialCut_partition y ht0 hb) ψ Z lam))
  have h43' := mul_le_mul_of_nonneg_left h43
    (mul_nonneg (sq_nonneg b⁻¹) neumannRemainderConstant_pos.le)
  have hfirst' := mul_le_mul_of_nonneg_left hfirst
    (by positivity : 0 ≤ (((2*Real.pi+1)/2)/b))
  linarith

def selectedPatchEnergyError {N : ℕ} (ψ : FormVector N) (y : Space) (a : ℝ)
    {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (Z lam : ℝ) (g : Space → ℝ) : ℝ :=
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let B := ∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ
  corePriceExcess Z lam ψ+
  (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2*((8*b/a)*B)^(1/2:ℝ)+
  b⁻¹^2*neumannRemainderConstant*(B^(2/3:ℝ)+B^(1/2:ℝ))+
  (((2*Real.pi+1)/2)/b)*B^(1/2:ℝ)+
  Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*Real.sqrt ((8*b/a)*B)+
  ((packetDirichlet g/2)*b⁻¹^2)*freshPatchMass p hp ψ Z lam y (t-4*b)

def selectedPotentialError {N : ℕ} (ψ : FormVector N) (y : Space) (a : ℝ)
    {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (Z lam q : ℝ) (g : Space → ℝ) : ℝ :=
  Real.sqrt ((2/q)*selectedPatchEnergyError ψ y a ht hb Z lam g)+
  (∫ x, rawLocalPotential y (q+Real.sqrt 3*b) x ∂formRawLaw ψ)+
  (2*Real.pi*tfPatchDensityCapConstant*q^2/(t-4*b)^6)+
  (∫ x, rawLocalPotential y (Real.sqrt 3*b) x ∂formRawLaw ψ)+
  Real.sqrt ((8*b/a)*(∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ))/(t-7*b)

theorem exists_selected_radial_potential_error {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hba : 7*b < 5*a) (hy : 6*a+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {q : ℝ} (hq : 0 < q) :
    ∃ t ∈ Icc (5*a) (6*a), ∃ ht : 0 ≤ t,
      radialPotentialError ψ y ht hb Z lam q ≤ selectedPotentialError ψ y a ht hb Z lam q g := by
  obtain ⟨t,ht,ht0,hd,hgap⟩ := selected_fresh_patch_budget_with_deletion
    hψ hm y ha hb hba hy hZ hlam hg hcg hgn hrad hgs
  refine ⟨t,ht,ht0,?_⟩
  have htb : 0 < t-7*b := by linarith [ht.1]
  have he := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 2/q))
  have hd' := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hd) htb.le
  simp only [radialPotentialError,hm,Real.sqrt_one,one_mul,mul_one,selectedPotentialError,
    selectedPatchEnergyError]
  exact add_le_add (add_le_add (add_le_add (add_le_add he le_rfl) le_rfl) le_rfl) hd'

theorem quantum_event_selected_master_center {Z : ℝ} (hZ : 0 ≤ Z) {N K : ℕ}
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
    {lam q : ℝ} (hlam : 0 < lam) (hq : 0 < q) (hqR : q ≤ 3*(5*a-4*b)/4) :
    ∃ G : fermionGraph N,
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell A))⁻¹ •
        Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
          (physicalObservationEvent ell A)) ∧
      formEnergy Z (graphFormVector G) ≤ energy Z N+
        (observationFisherConstant/2)*(∑ k, ((ell k)⁻¹)^2)*
          (Real.log (Real.exp 1/physicalObservationProbability F ell A))^5 ∧
      ∃ t ∈ Icc (5*a) (6*a), ∃ ht : 0 ≤ t,
      |Z/‖y‖-lam-(physicalObservationProbability F ell A)⁻¹*
        (∫ z in physicalObservationEvent ell A,
          tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g (originalDatum ell j z)) y
          ∂physicalObservationLaw (graphRawLaw F) K)-
        expectedRadialPatchCenter (graphFormVector G) y ht hb Z lam| ≤
        selectedPotentialError (graphFormVector G) y a ht hb Z lam q g+
        (∫ x, rawLocalPotential y (2*masterWidth c₁ r₀ s y) x ∂graphRawLaw G) := by
  obtain ⟨G,hG,hlaw,hE⟩ := quantum_physical_observation_event_tilt hZ F hn hF ell hell hA hsy hp
  have hmass : formMass (graphFormVector G) = 1 := (formMass_graph G).trans hG
  obtain ⟨t,ht,ht0,herr⟩ := exists_selected_radial_potential_error
    (graphFormVector_sobolev G) hmass y ha hb hba hy hZ hlam hg hcg hgn hrad hgs hq
  refine ⟨G,hG,hlaw,hE,t,ht,ht0,?_⟩
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
  simpa only [hmass,mul_one,formRawLaw_graph] using hh'

end CoulombAtom

end

end OAI
