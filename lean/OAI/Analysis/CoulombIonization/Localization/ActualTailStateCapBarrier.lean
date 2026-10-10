import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.ExpectedPatchCenter
import OAI.Analysis.CoulombIonization.RadialBounds.ActualTailTiltBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ActualTailStateCap_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem TailTiltState.posterior_cap {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) :
      ∀ (j : Fin (K+1)) (y : Space) (_hy : y ≠ 0) (_ha1 : localCellRadius y ≤ 1)
        (_hry : r₀ ≤ ‖y‖) (b q θ : ℝ) (_hb : 0 < b) (_hba : 2*b ≤ localCellRadius y)
        (_hq : 0 < q) (_hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
        (_hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
        (_hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3)),
      tfPatchCapConstant/(localCellRadius y)^4+
        (sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) q+
        sharpLocalPotentialBudget (localCellRadius y)
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (2*masterWidth c₁ r₀ s y)) < θ →
      ((physicalObservationLaw (graphRawLaw F) K)
        {z | θ < Z/‖y‖-lam-tfPotential (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
            (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z)) y}).toReal < p₀ j := by
  intro j y hy ha1 hry b q θ hb hba hq hqr hqR hcollar hsmall
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let P := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
      (originalDatum ell j z)) y
  let A := {z | θ < Z/‖y‖-lam-P z}
  have hA : MeasurableSet[observationInformation ell j] A :=
    measurableSet_lt measurable_const (measurable_const.sub
      (jointMasterPosterior_potential_measurable (graphRawLaw F) ell j y hc hr₀ hs canonicalRealPacket_smooth.continuous))
  obtain ⟨B,hB,hBA⟩ := observation_event_tail_representation ell j hA
  let p := ((physicalObservationLaw (graphRawLaw F) K) A).toReal
  have hpB : physicalObservationProbability F ell B = p := by
    change ((physicalObservationLaw (graphRawLaw F) K) (physicalObservationEvent ell B)).toReal = p
    rw [hBA]
  change p < p₀ j
  by_contra! hn
  have hp : 0 < p := (h₀ j).trans_le hn
  obtain ⟨G,hGn,hlaw,hDE⟩ := hstate.2.2 j A hA hn
  rw [←hBA] at hlaw
  have hcollar' : localCellRadius y ≤ b^2*localOffsetMass
      (max (corePriceExcess Z lam (graphFormVector G)) 0) y := by
    apply hcollar.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
    unfold localOffsetMass
    linarith [le_max_left (1/(localCellRadius y)^3) 1,Real.sqrt_nonneg
      (max (corePriceExcess Z lam (graphFormVector G)) 0*localCellRadius y)]
  have hupper := sharp_eventLaw_field_cap hZ hlam F G hGn ell j
    (by rwa [hBA]) (by rwa [hpB]) hlaw hy ha1 hc hcL hr₀ hs hs1 hry hb hba hq hqr hqR hcollar'
  have herror := sharp_combined_error_mono hy hb hq hDE
    (by linarith [masterWidth_pos hc hr₀ hs y] : 0 ≤ 2*masterWidth c₁ r₀ s y)
  rw [hpB,hBA] at hupper
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  have hPi : Integrable P (physicalObservationLaw (graphRawLaw F) K) :=
    jointMasterPosterior_potential_integrable (graphRawLaw F) ell j y hi he hc hr₀ hs
      canonicalRealPacket_smooth canonicalRealPacket_compact canonicalRealPacket_normalized
        canonicalRealPacket_radial canonicalRealPacket_support
  have hlower := threshold_event_mean_ge (physicalObservationLaw (graphRawLaw F) K)
    ((integrable_const (Z/‖y‖-lam)).sub hPi) ((observationInformation_le ell j) A hA)
    (fun z hz => hz.le) hp
  simp only [Pi.sub_apply] at hlower
  rw [normalized_setIntegral_const_sub _ A hPi hp] at hlower
  exact (not_le_of_gt (lt_of_le_of_lt (hupper.trans (add_le_add le_rfl herror)) hsmall)) hlower

end Work_ActualTailStateCap_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

open CoulombAnalysis CoulombNeumann

theorem conditional_high_mean_expected_center_on_support {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R b : ℝ} (hR : 0 < R) (hb : 0 < b)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) (Z lam : ℝ)
    (S : Configuration M → Finset (Fin M))
    (hi : Integrable (weightedPatchGap ψ t Z lam y R hb S))
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H eta m : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q)
    (hqR : q ≤ R/12) (hsmall : tfPatchOscillationConstant/R*q ≤ 1/2)
    (hH : 0 ≤ H) (heta : 0 < eta) (hm : 0 < m)
    (hcount : ∀ᵐ u, formMass (coreSlice ψ t u) ≠ 0 → m ≤ ∫ z in ball (0 : Space) q,
      retainedPatchLp hb (S u) u y R z ∂ballMeasure R)
    (hhigh : ∀ᵐ u, formMass (coreSlice ψ t u) ≠ 0 →
      (max (H+(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R)+Real.sqrt ((16*q^3*(L:ℝ)^2)*eta) <
        ∫ x, k x*retainedPatchLp hb (S u) u y R x ∂ballMeasure R) :
    H*(∫ u, formMass (coreSlice ψ t u))-
      (H/eta+2/m)*(∫ u, weightedPatchGap ψ t Z lam y R hb S u)-
      (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4)*(∫ u, formMass (coreSlice ψ t u)) ≤
      ∫ u, weightedPatchCenter ψ t Z lam y R u := by
  have hOsc := tfPatchOscillationConstant_pos
  have hbound : ∀ᵐ u,
      H*formMass (coreSlice ψ t u)-(H/eta+2/m)*weightedPatchGap ψ t Z lam y R hb S u-
        (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4)*formMass (coreSlice ψ t u) ≤
      weightedPatchCenter ψ t Z lam y R u := by
    filter_upwards [hψ.ae_coreSlice t,hcount,hhigh] with u hu hcu hhu
    by_cases hmass : formMass (coreSlice ψ t u) = 0
    · simp only [weightedPatchCenter,weightedPatchGap,hmass,zero_mul,
        mul_zero,sub_zero,le_refl]
    let D := tfPatchGap R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u) (retainedPatchLp hb (S u) u y R)
    have hn := conditionalPatchMinimizer_negative_center ψ t u hu A (hcore u) y hR hb hb hnuc hsep Z lam
      (retainedPatchLp_nonneg hb (S u) u y R) hq hqR hsmall hm (hcu hmass)
    have hg : D ≤ eta → H ≤ conditionalPatchCenter ψ t Z lam y R u := by
      intro hD
      apply le_of_lt
      apply conditionalPatch_high_center ψ t u hu A (hcore u) y hR hb hb hnuc hsep Z lam
        (retainedPatchLp_nonneg hb (S u) u y R) hk hkn hq hs hqR (hsmall.trans (by norm_num)) hH
      exact (add_le_add le_rfl (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 16*q^3*(L:ℝ)^2)))).trans_lt (hhu hmass)
    have he := field_lower_from_good_gap
      (tfPatchGap_nonneg R tfKinetic tfKinetic_pos _ (retainedPatchLp_nonneg hb (S u) u y R))
      hH heta (by positivity : 0 ≤ 2/m)
      (by positivity : 0 ≤ 2*(tfPatchOscillationConstant/R*q)*R⁻¹^4) hg
      (by simpa only [conditionalPatchCenter,add_zero] using hn)
    have he' := mul_le_mul_of_nonneg_left he (formMass_nonneg (coreSlice ψ t u))
    dsimp only [weightedPatchCenter,weightedPatchGap,D] at he' ⊢
    nlinarith
  have hmassi := hψ.coreSlice_mass_integrable t
  have hfirst : Integrable (fun u => H*formMass (coreSlice ψ t u)-
      (H/eta+2/m)*weightedPatchGap ψ t Z lam y R hb S u) :=
    (hmassi.const_mul H).sub (hi.const_mul (H/eta+2/m))
  have hleft := hfirst.sub
    (hmassi.const_mul (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4))
  have he := integral_mono_ae hleft
    (weightedPatchCenter_integrable hψ t y hR Z lam hb A hcore hnuc hsep) hbound
  simp only [Pi.sub_apply] at he
  rw [integral_sub hfirst
    (hmassi.const_mul (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4)),
    integral_sub (hmassi.const_mul H) (hi.const_mul (H/eta+2/m)),
    integral_const_mul,integral_const_mul,integral_const_mul] at he
  exact he

theorem conditional_low_mean_expected_center_on_support {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R b : ℝ} (hR : 0 < R) (hb : 0 < b)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) (Z lam : ℝ)
    (S : Configuration M → Finset (Fin M))
    (hi : Integrable (weightedPatchGap ψ t Z lam y R hb S))
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H eta : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q)
    (hqR : q ≤ R/12) (hH : 0 ≤ H) (heta : 0 < eta)
    (hlow : ∀ᵐ u, formMass (coreSlice ψ t u) ≠ 0 → (∫ x, k x*retainedPatchLp hb (S u) u y R x ∂ballMeasure R)+
        Real.sqrt ((16*q^3*(L:ℝ)^2)*eta) <
      (max (H-(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R)) :
    (∫ u, weightedPatchCenter ψ t Z lam y R u) ≤
      H*(∫ u, formMass (coreSlice ψ t u))+
        ((tfPatchCapConstant/R^4)/eta)*(∫ u, weightedPatchGap ψ t Z lam y R hb S u) := by
  have hCap := tfPatchCapConstant_pos
  have hbound : ∀ᵐ u,
      weightedPatchCenter ψ t Z lam y R u ≤
      H*formMass (coreSlice ψ t u)+((tfPatchCapConstant/R^4)/eta)*weightedPatchGap ψ t Z lam y R hb S u := by
    filter_upwards [hψ.ae_coreSlice t,hlow] with u hu hlu
    by_cases hmass : formMass (coreSlice ψ t u) = 0
    · simp only [weightedPatchCenter,weightedPatchGap,hmass,zero_mul,
        mul_zero,add_zero,le_refl]
    let D := tfPatchGap R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u) (retainedPatchLp hb (S u) u y R)
    have hc := conditionalPatchMinimizer_nonradial_cap ψ t u hu A (hcore u) y hR hb hb hnuc hsep Z lam 0
      (by simpa only [norm_zero] using (by positivity : 0 ≤ 3*R/4))
    have hg : D ≤ eta → conditionalPatchCenter ψ t Z lam y R u ≤ H := by
      intro hD
      apply le_of_lt
      apply conditionalPatch_low_center ψ t u hu A (hcore u) y hR hb hb hnuc hsep Z lam
        (retainedPatchLp_nonneg hb (S u) u y R) hk hkn hq hs hqR hH
      exact (add_le_add le_rfl (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 16*q^3*(L:ℝ)^2)))).trans_lt (hlu hmass)
    have he := field_upper_from_good_gap
      (tfPatchGap_nonneg R tfKinetic tfKinetic_pos _ (retainedPatchLp_nonneg hb (S u) u y R))
      hH heta (by positivity : 0 ≤ tfPatchCapConstant/R^4) hg
      (by simpa only [conditionalPatchCenter,add_zero] using hc)
    have he' := mul_le_mul_of_nonneg_left he (formMass_nonneg (coreSlice ψ t u))
    dsimp only [weightedPatchCenter,weightedPatchGap,D] at he' ⊢
    nlinarith
  have hmassi := hψ.coreSlice_mass_integrable t
  have hright := (hmassi.const_mul H).add (hi.const_mul ((tfPatchCapConstant/R^4)/eta))
  have he := integral_mono_ae
    (weightedPatchCenter_integrable hψ t y hR Z lam hb A hcore hnuc hsep) hright hbound
  simp only [Pi.add_apply] at he
  rw [integral_add (hmassi.const_mul H) (hi.const_mul ((tfPatchCapConstant/R^4)/eta)),
    integral_const_mul,integral_const_mul] at he
  exact he

end CoulombAtom

end

end OAI
