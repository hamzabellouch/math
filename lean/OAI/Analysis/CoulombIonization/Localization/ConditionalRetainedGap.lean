import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.PatchMass
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchRandomVariables
import OAI.Analysis.CoulombIonization.FieldAnalysis.ConditionalObservables
import OAI.Analysis.CoulombIonization.Ionization.ConditionalPatchMinimizer
import OAI.Analysis.CoulombIonization.FieldAnalysis.RetainedFieldIdentity

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ConditionalRetainedGap_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff ENNReal

open CoulombAnalysis CoulombNeumann

theorem conditional_retained_patch_gap {M N : ℕ} {ψ : FormVector M}
    (hψ : SobolevFermion ψ) (y : Space) (R : ℝ) (Φ : TFField R)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hΦ : Φ =ᵐ[ballMeasure R] fun z => normalizedCoreField Z lam ψ (y+z))
    {F : ℝ} (hF : ∀ᵐ z ∂ballMeasure R, Φ z ≤ F)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space) (hcore : ∀ u i, u i ∉ A → FormZeroAt ψ u)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖)
    (S : Finset (Fin N)) (x : Configuration N)
    (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R)
    (hret_nuc : ∀ i ∈ S, Real.sqrt 3*b ≤ ‖x i‖)
    (hret_core : ∀ i ∈ S, ∀ a ∈ A, Real.sqrt 3*b ≤ ‖a-x i‖) :
    let σ := retainedPatchLp hb S x y R
    let ρ := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
    formMass ψ*((1/2:ℝ)*tfCoulombL R (σ-ρ) (σ-ρ)+
      (∫ z, max (tfBallPotential R ρ z-Φ z) 0*σ z ∂ballMeasure R)) ≤
      formEnergy Z ψ+lam*M*formMass ψ-priceEnergy (energy Z) lam*formMass ψ+
        formMass ψ*(tfKinetic*retainedPressure b S x-
          (∑ i ∈ S, normalizedCoreField Z lam ψ (x i))+
          (1/2:ℝ)*(∫ p : Space × Space,
            retainedSmear b S x p.1*retainedSmear b S x p.2/‖p.1-p.2‖)+
          (packetDirichlet g/2)*b⁻¹^2*(∫ z, ρ z ∂ballMeasure R)) := by
  dsimp only
  have hu := conditional_priced_patch_minimizer_upper hψ y R Φ hZ hlam hΦ hF
    hg hcg hgn hr hgs hb A hcore hsep hnuc hcs
  have hg := mul_le_mul_of_nonneg_left
    (tfPatchFunctional_clipping_gap R Φ tfKinetic_pos (retainedPatchLp_nonneg hb S x y R))
    (formMass_nonneg ψ)
  rw [retainedPatchLp_functional hb S x y hmargin Φ (normalizedCoreField Z lam ψ) hΦ tfKinetic,
    retainedSmear_core_field hψ.sobolevVector hb S x A hcore hret_nuc hret_core Z lam] at hg
  dsimp only at hu
  nlinarith

theorem actual_retained_patch_gap {M N : ℕ} {ψ : FormVector M}
    (hψ : SobolevFermion ψ) (y : Space) (R : ℝ)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space) (hcore : ∀ u i, u i ∉ A → FormZeroAt ψ u)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖)
    (S : Finset (Fin N)) (x : Configuration N)
    (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R)
    (hret_nuc : ∀ i ∈ S, Real.sqrt 3*b ≤ ‖x i‖)
    (hret_core : ∀ i ∈ S, ∀ a ∈ A, Real.sqrt 3*b ≤ ‖a-x i‖) :
    let hfield := normalizedCoreField_memLp_patch hψ.sobolevVector A hcore y R hb hb hnuc hcs Z lam
    let Φ := hfield.toLp (fun z => normalizedCoreField Z lam ψ (y+z))
    let σ := retainedPatchLp hb S x y R
    let ρ := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
    formMass ψ*((1/2:ℝ)*tfCoulombL R (σ-ρ) (σ-ρ)+
      (∫ z, max (tfBallPotential R ρ z-Φ z) 0*σ z ∂ballMeasure R)) ≤
      formEnergy Z ψ+lam*M*formMass ψ-priceEnergy (energy Z) lam*formMass ψ+
        formMass ψ*(tfKinetic*retainedPressure b S x-
          (∑ i ∈ S, normalizedCoreField Z lam ψ (x i))+
          (1/2:ℝ)*(∫ p : Space × Space,
            retainedSmear b S x p.1*retainedSmear b S x p.2/‖p.1-p.2‖)+
          (packetDirichlet g/2)*b⁻¹^2*(∫ z, ρ z ∂ballMeasure R)) := by
  dsimp only
  let hfield := normalizedCoreField_memLp_patch hψ.sobolevVector A hcore y R hb hb hnuc hcs Z lam
  have hbound : ∀ᵐ z ∂ballMeasure R,
      hfield.toLp (fun z => normalizedCoreField Z lam ψ (y+z)) z ≤ |Z|/b+|lam|+M/b := by
    filter_upwards [hfield.coeFn_toLp,ae_restrict_mem measurableSet_ball] with z hz hmem
    rw [hz]
    have hz' : y+z ∈ closedBall y R := by
      simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left] using
        (show ‖z‖ ≤ R from (by simpa only [mem_ball,dist_eq_norm,sub_zero] using hmem : ‖z‖ < R).le)
    exact (le_abs_self _).trans (normalizedCoreField_abs_le hψ.sobolevVector A hcore hb
      (y+z) (fun a ha => hcs a ha _ hz') hb (hnuc _ hz') Z lam)
  exact conditional_retained_patch_gap hψ y R _ hZ hlam hfield.coeFn_toLp hbound
    hg hcg hgn hr hgs hb A hcore hsep hnuc hcs S x hmargin hret_nuc hret_core

end Work_ConditionalRetainedGap_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

def finiteCorePatchBound (N : ℕ) (Z lam b : ℝ) : ℝ := |Z|/b+|lam|+N/b

lemma finiteCorePatchBound_nonneg (N : ℕ) (Z lam : ℝ) {b : ℝ} (hb : 0 < b) :
    0 ≤ finiteCorePatchBound N Z lam b := by unfold finiteCorePatchBound; positivity

lemma conditionalPatchField_upper {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) (R : ℝ) (Z lam : ℝ)
    {b : ℝ} (hb : 0 < b) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    ∀ᵐ u : Configuration M, ∀ᵐ z ∂ballMeasure R,
      conditionalPatchField ψ t Z lam y R u z ≤ finiteCorePatchBound N Z lam b := by
  apply (hψ.ae_coreSlice t).mono
  intro u hu
  have hf := normalizedCoreField_memLp_patch hu A (hcore u) y R hb hb hnuc hcs Z lam
  filter_upwards [conditionalPatchField_ae ψ t Z lam y R u hf,
    ae_restrict_mem measurableSet_ball] with z hz hmem
  have hpos : y+z ∈ closedBall y R := by
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left] using
      ((mem_ball_zero_iff.mp hmem).le)
  rw [hz]
  exact (le_abs_self _).trans (normalizedCoreField_abs_le hu A (hcore u) hb (y+z)
    (fun a ha => hcs a ha _ hpos) hb (hnuc _ hpos) Z lam)

def weightedPatchMass {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) (u : Configuration M) : ℝ :=
  formMass (coreSlice ψ t u)*(∫ z,
    tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) z ∂ballMeasure R)

lemma weightedPatchMass_nonneg {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) (u : Configuration M) :
    0 ≤ weightedPatchMass ψ t Z lam y R u :=
  mul_nonneg (formMass_nonneg _) (integral_nonneg_of_ae (tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos _))

lemma weightedPatchMass_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) {R : ℝ} (hR : 0 < R) (Z lam : ℝ)
    {b : ℝ} (hb : 0 < b) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    Integrable (weightedPatchMass ψ t Z lam y R) := by
  have hm := (conditionalPatchMass_aemeasurable hψ t Z lam y R).aestronglyMeasurable
  have hbnd : ∀ᵐ u : Configuration M, ‖(∫ z,
      tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) z ∂ballMeasure R)‖ ≤
      4*R*finiteCorePatchBound N Z lam b := by
    apply (conditionalPatchField_upper hψ t y R Z lam hb A hcore hnuc hcs).mono
    intro u hu
    rw [Real.norm_of_nonneg (integral_nonneg_of_ae (tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos _))]
    exact tfPatchMinimizer_mass_le hR tfKinetic_pos (finiteCorePatchBound_nonneg N Z lam hb) _ hu
  exact ((hψ.coreSlice_mass_integrable t).bdd_mul hm hbnd).congr
    (Eventually.of_forall fun _ => mul_comm _ _)

lemma coreSlice_priceExcess_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) :
    Integrable (fun u => corePriceExcess Z lam (coreSlice ψ t u)) := by
  exact ((hψ.coreSlice_energy_integrable Z t).add ((hψ.coreSlice_mass_integrable t).const_mul (lam*N))).sub
    ((hψ.coreSlice_mass_integrable t).const_mul (priceEnergy (energy Z) lam))

def weightedPatchGap {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (u : Configuration M) : ℝ :=
  formMass (coreSlice ψ t u)*tfPatchGap R tfKinetic tfKinetic_pos
    (conditionalPatchField ψ t Z lam y R u) (retainedPatchLp hb (S u) u y R)

lemma weightedPatchGap_nonneg {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (u : Configuration M) :
    0 ≤ weightedPatchGap ψ t Z lam y R hb S u :=
  mul_nonneg (formMass_nonneg _) (tfPatchGap_nonneg _ _ _ _ (retainedPatchLp_nonneg hb (S u) u y R))

theorem conditionalPatchGap_upper {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (ha : CoreAntisymmetric ψ) (t : Spins M)
    (y : Space) (R : ℝ) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space) (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖)
    (S : Configuration M → Finset (Fin M))
    (hmargin : ∀ u, ∀ i ∈ S u, ‖u i-y‖+Real.sqrt 3*b ≤ R)
    (hret_nuc : ∀ u, ∀ i ∈ S u, Real.sqrt 3*b ≤ ‖u i‖)
    (hret_core : ∀ u, ∀ i ∈ S u, ∀ a ∈ A, Real.sqrt 3*b ≤ ‖a-u i‖) :
    ∀ᵐ u : Configuration M,
      weightedPatchGap ψ t Z lam y R hb S u ≤
      corePriceExcess Z lam (coreSlice ψ t u)+
        tfKinetic*(retainedPressure b (S u) u*formMass (coreSlice ψ t u))-
        conditionalRetainedFieldSum Z lam ψ t S u+
        retainedDirect b (S u) u*formMass (coreSlice ψ t u)+
        ((packetDirichlet g/2)*b⁻¹^2)*weightedPatchMass ψ t Z lam y R u := by
  filter_upwards [ha.ae_coreSlice hψ t,
    conditionalPatchField_upper hψ t y R Z lam hb A hcore hnuc hcs] with u hu hfield
  have hf := normalizedCoreField_memLp_patch hu.sobolevVector A (hcore u) y R hb hb hnuc hcs Z lam
  have hh := conditional_retained_patch_gap hu y R (conditionalPatchField ψ t Z lam y R u)
    hZ hlam (conditionalPatchField_ae ψ t Z lam y R u hf) hfield
    hg hcg hgn hr hgs hb A (hcore u) hsep hnuc hcs (S u) u
    (hmargin u) (hret_nuc u) (hret_core u)
  dsimp only at hh
  change formMass (coreSlice ψ t u)*_ ≤ _
  unfold tfPatchGap
  unfold corePriceExcess conditionalRetainedFieldSum retainedDirect weightedPatchMass
  nlinarith

theorem weightedPatchGap_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (ha : CoreAntisymmetric ψ) (t : Spins M)
    (y : Space) {R : ℝ} (hR : 0 < R) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space) (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (hmargin : ∀ u, ∀ i ∈ S u, ‖u i-y‖+Real.sqrt 3*b ≤ R)
    (hret_nuc : ∀ u, ∀ i ∈ S u, Real.sqrt 3*b ≤ ‖u i‖)
    (hret_core : ∀ u, ∀ i ∈ S u, ∀ a ∈ A, Real.sqrt 3*b ≤ ‖a-u i‖) :
    Integrable (weightedPatchGap ψ t Z lam y R hb S) := by
  have hm := (hψ.coreSlice_mass_integrable t).aemeasurable.mul
    (conditionalPatchGap_aemeasurable hψ t Z lam y R hb S hS)
  have hi := ((((coreSlice_priceExcess_integrable hψ t Z lam).add
    ((retained_pressure_weighted_integrable hψ hb t S hS).const_mul tfKinetic)).sub
    (conditionalRetainedFieldSum_integrable hψ Z lam t S hS)).add
    (retained_direct_weighted_integrable hψ hb t S hS)).add
    ((weightedPatchMass_integrable hψ t y hR Z lam hb A hcore hnuc hcs).const_mul
      ((packetDirichlet g/2)*b⁻¹^2))
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [conditionalPatchGap_upper hψ ha t y R hZ hlam hg hcg hgn hr hgs
    hb A hcore hsep hnuc hcs S hmargin hret_nuc hret_core] with u hu
  simp only [Pi.mul_apply,Pi.add_apply,Pi.sub_apply]
  change ‖weightedPatchGap ψ t Z lam y R hb S u‖ ≤ _
  rw [Real.norm_of_nonneg (weightedPatchGap_nonneg ψ t Z lam y R hb S u)]
  exact hu

end CoulombAtom

end

end OAI
