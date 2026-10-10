import Mathlib
import OAI.Analysis.CoulombRadii.Packets.OriginalPotentialTower
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalRetainedLikelihood

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

lemma fromH1_raw_bounded_integral {n : ℕ} (u : Coulomb.H1Vector n)
    {F : Configuration n → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ x, ‖F x‖≤C) :
    (∫ x,F x ∂rawLaw (fromH1Wave u))=
      Coulomb.potentialForm (fun x => F ((flattenConfiguration n).symm x)) u := by
  have hu (σ : Spins n) : MemLp (fromH1Wave u σ) 2 volume :=
    (u.value_L2 σ).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  rw [integral_rawLaw hu,rawExpectation_eq_stateWeightedIntegral hu hF hC]
  unfold stateWeightedIntegral Coulomb.potentialForm
  apply Finset.sum_congr rfl
  intro σ _
  have H := (flattenConfiguration_measurePreserving n).integral_comp'
    (fun x => F ((flattenConfiguration n).symm x)*‖u.value σ x‖^2)
  change (∫ x : Configuration n, F ((flattenConfiguration n).symm (flattenConfiguration n x))*
    ‖fromH1Wave u σ x‖^2)=_ at H
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using H

theorem retainedEvent_potential_mean {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0<r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B)
    (u : Coulomb.H1Vector n) (hum : Coulomb.mass u=1)
    (hlaw : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood
        (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ)) (retainedTailObservation j ⁻¹' B)))⁻¹*
      stateWeightedIntegral ψ (fun x => arrayEventLikelihood
        (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ)) (retainedTailObservation j ⁻¹' B) x*
        F (flattenConfiguration n x)))
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0<c) (hr₀ : 0<r₀) (hs : 0<s) (y : Position) :
    letI := rawLaw_isProbability hψ hn
    potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y=
      ((observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B))⁻¹*
        ∫ z in tailObservation r j ⁻¹' B,
          potentialOf (conditionalPacketDensity (observationLaw J (rawLaw ψ)) Prod.fst
            (tailObservation r j) g c r₀ s (tailObservation r j z)) y ∂observationLaw J (rawLaw ψ) := by
  let := rawLaw_isProbability hψ hn
  have hu (σ : Spins n) : MemLp (fromH1Wave u σ) 2 volume :=
    (u.value_L2 σ).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  have := rawLaw_isProbability hu ((fromH1_mass u).trans hum)
  obtain ⟨C,hC,H⟩ := rawPacketPotential_uniform (n:=n) hg hgs hm hc hr₀ hs
  have hF := measurable_rawPacketPotential (n:=n) hg hc hr₀ hs y
  have hbound (x : Configuration n) : ‖potentialOf (rawPacketDensity g c r₀ s x) y‖≤C := by
    rw [Real.norm_of_nonneg (H x y).2.1]
    exact (H x y).2.2
  rw [mixturePacketPotential hg hgs hm hc hr₀ hs,fromH1_raw_bounded_integral u hF hbound,hlaw]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [←physical_retainedTailEvent_probability hψ hn r hr j hB,
    ←physical_retainedTailEvent_bayes_integral hψ hn r hr j hB hF hbound,
    integral_indicator (hB.preimage (measurable_tailObservation r j))]
  congr 1
  exact (physical_observation_potential_tower (rawLaw ψ) r j hg hgs hm hc hr₀ hs
    (show MeasurableSet[observationSigma r j] (tailObservation r j ⁻¹' B) from ⟨B,hB,rfl⟩) y).symm

lemma conditionalPacketPotential_integrable {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → B}
    (hraw : MeasurePreserving raw P ν) (hobs : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ} (hc : 0<c) (hr : 0<r₀) (hs : 0<s)
    (y : Position) :
    Integrable (fun sample => potentialOf (conditionalPacketDensity P raw obs g c r₀ s (obs sample)) y) P :=
  (integrable_condExp (f:=fun sample => potentialOf (rawPacketDensity g c r₀ s (raw sample)) y)).congr
    (conditionalPacketPotential_eq_condExp P ν hraw hobs hg hgs hm hc hr hs y).symm

lemma normalized_event_const_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {A : Set Ω} {f : Ω → ℝ} (hi : Integrable f P)
    (hp : 0<P.real A) (C : ℝ) :
    (P.real A)⁻¹*(∫ x in A,C-f x ∂P)=C-(P.real A)⁻¹*(∫ x in A,f x ∂P) := by
  rw [integral_sub (integrable_const C) hi.integrableOn,integral_const]
  simp only [smul_eq_mul,measureReal_restrict_apply_univ]
  rw [mul_sub,←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]

lemma normalized_event_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A) {f : Ω → ℝ}
    (hi : Integrable f P) (hp : 0<P.real A) {v : ℝ}
    (hb : ∀ᵐ x ∂P, x∈A → f x≤v) :
    (P.real A)⁻¹*(∫ x in A,f x ∂P)≤v := by
  have h := setIntegral_mono_ae_restrict hi.integrableOn (integrable_const v)
    ((ae_restrict_iff' hA).mpr hb)
  rw [integral_const] at h
  simp only [smul_eq_mul,measureReal_restrict_apply_univ] at h
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul] using hh

lemma le_normalized_event {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A) {f : Ω → ℝ}
    (hi : Integrable f P) (hp : 0<P.real A) {v : ℝ}
    (hb : ∀ᵐ x ∂P, x∈A → v≤f x) :
    v≤(P.real A)⁻¹*(∫ x in A,f x ∂P) := by
  have h := setIntegral_mono_ae_restrict (integrable_const v) hi.integrableOn
    ((ae_restrict_iff' hA).mpr hb)
  rw [integral_const] at h
  simp only [smul_eq_mul,measureReal_restrict_apply_univ] at h
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul] using hh

theorem retainedEvent_field_mean {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0<r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B)
    (u : Coulomb.H1Vector n) (hum : Coulomb.mass u=1)
    (hlaw : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood
        (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ)) (retainedTailObservation j ⁻¹' B)))⁻¹*
      stateWeightedIntegral ψ (fun x => arrayEventLikelihood
        (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ)) (retainedTailObservation j ⁻¹' B) x*
        F (flattenConfiguration n x)))
    (hp : 0<(observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B))
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0<c) (hr₀ : 0<r₀) (hs : 0<s) (y : Position) (V : ℝ) :
    letI := rawLaw_isProbability hψ hn
    V-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y=
      ((observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B))⁻¹*
        ∫ z in tailObservation r j ⁻¹' B,
          V-potentialOf (conditionalPacketDensity (observationLaw J (rawLaw ψ)) Prod.fst
            (tailObservation r j) g c r₀ s (tailObservation r j z)) y ∂observationLaw J (rawLaw ψ) := by
  let := rawLaw_isProbability hψ hn
  rw [normalized_event_const_sub
    (conditionalPacketPotential_integrable (observationLaw J (rawLaw ψ)) (rawLaw ψ)
      (observationLaw_rawProjection _) (measurable_tailObservation r j) hg hgs hm hc hr₀ hs y) hp]
  rw [retainedEvent_potential_mean hψ hn r hr j hB u hum hlaw hg hgs hm hc hr₀ hs y]

end NeutralAtom

end

end

end OAI
