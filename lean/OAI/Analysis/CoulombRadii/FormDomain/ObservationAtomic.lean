import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.UniformScreening
import OAI.Analysis.CoulombRadii.Variational.PhysicalBridge
import OAI.Analysis.CoulombRadii.RandomFields.EventTiltWavefunction

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma asH1_potentialForm {n : ℕ} (ψ : Wavefunction n) (g : Gradient n)
    (hw : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hg : ∀ σ i a, MemLp (g σ i a) 2 volume) (B : Coulomb.Configuration n → ℝ) :
    Coulomb.potentialForm B (asH1 ψ g hw hψ hg) =
      stateWeightedIntegral ψ (fun x => B (flattenConfiguration n x)) := by
  unfold Coulomb.potentialForm stateWeightedIntegral
  apply Finset.sum_congr rfl
  intro σ _
  change (∫ x, B x*‖ψ σ ((flattenConfiguration n).symm x)‖^2) = _
  have H := (flattenConfiguration_symm_measurePreserving n).integral_comp'
    (fun x => B (flattenConfiguration n x)*‖ψ σ x‖^2)
  change (∫ x, B (flattenConfiguration n ((flattenConfiguration n).symm x))*
    ‖ψ σ ((flattenConfiguration n).symm x)‖^2) = _ at H
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using H

lemma eventTilt_stateWeightedIntegral {n : ℕ} (ψ : Wavefunction n)
    {F : Configuration n → ℝ} (hF : ∀ x, 0 ≤ F x)
    (hp : 0 < stateWeightedIntegral ψ F) (B : Configuration n → ℝ) :
    stateWeightedIntegral (eventTiltWavefunction ψ F) B =
      (stateWeightedIntegral ψ F)⁻¹ * stateWeightedIntegral ψ (fun x => F x*B x) := by
  unfold stateWeightedIntegral
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [eventTiltWavefunction_raw_density ψ hF hp]
  simp only [stateWeightedIntegral]
  ring

theorem atomic_arrayEvent_state {H : Type*} [Fintype H] {n : ℕ}
    (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n),
      FormDomain χ h → normSquared χ=1 → energy Z ψ g ≤ energy Z χ h)
    {E D₀ : ℝ} (hbase : energy Z ψ g ≤ E+D₀)
    (ℓ : H → ℝ) (hℓ : ∀ h, 0 < ℓ h)
    {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (hsym : ∀ (p : Equiv.Perm (Fin n)) y, permuteObservationArray p y∈s ↔ y∈s)
    (hp : 0 < stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)) :
    ∃ u : Coulomb.H1Vector n, Coulomb.Antisymmetric u ∧ Coulomb.mass u=1 ∧
      Coulomb.form (Coulomb.atom Z hZ) u ≤ E+(D₀+observationEventEnergyConstant*
        observationWidthSquareSum ℓ*(1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5) ∧
      ∀ B : Coulomb.Configuration n → ℝ,
        Coulomb.potentialForm B u = (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s))⁻¹*
          stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ s x*B (flattenConfiguration n x)) := by
  obtain ⟨hdom,hmass,henergy⟩ := groundState_arrayEventTilt Z hd hn hmin ℓ hℓ hs hsym hp
  let u := asH1 (eventTiltWavefunction ψ (arrayEventLikelihood ℓ s))
    (eventTiltGradient ψ g (arrayEventLikelihood ℓ s)) hdom.2.1 hdom.2.2.1 hdom.2.2.2.1
  refine ⟨u,asH1_antisymmetric hdom,(asH1_mass ..).trans hmass,?_,?_⟩
  · change Coulomb.form (Coulomb.atom Z hZ) (asH1 ..) ≤ _
    rw [asH1_energy Z hZ]
    linarith
  · intro B
    rw [asH1_potentialForm,eventTilt_stateWeightedIntegral ψ (arrayEventLikelihood_nonneg ℓ hs) hp]

lemma observationEventOffset_nonneg {H : Type*} [Fintype H] {n : ℕ}
    {ψ : Wavefunction n} {g : Gradient n} (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    {D₀ : ℝ} (hD : 0 ≤ D₀) (ℓ : H → ℝ)
    {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (hp : 0 < stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)) :
    0 ≤ D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*
      (1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5 := by
  have h1 := stateWeightedIntegral_le_one hd hn (arrayEventLikelihood_contDiff ℓ hs).continuous.measurable
    (arrayEventLikelihood_nonneg ℓ hs) (arrayEventLikelihood_le_one ℓ hs)
  have hl := Real.log_nonpos hp.le h1
  exact add_nonneg hD (mul_nonneg (mul_nonneg observationEventEnergyConstant_pos.le
    (observationWidthSquareSum_nonneg ℓ)) (pow_nonneg (by linarith) _))

theorem atomic_arrayEvent_annular_second_moment {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : Type*} [Fintype H] {n : ℕ}
    (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n},
    FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ : Wavefunction n) (h : Gradient n),
      FormDomain χ h → normSquared χ=1 → energy Z ψ g ≤ energy Z χ h) →
    ∀ {E D₀ : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D₀ → 0 ≤ D₀ → ∀ (ℓ : H → ℝ), (∀ h, 0 < ℓ h) →
    ∀ {s : Set ((H × (Fin n × Fin 3)) → ℝ)}, MeasurableSet s →
    (∀ (p : Equiv.Perm (Fin n)) y, permuteObservationArray p y∈s ↔ y∈s) →
    0 < stateWeightedIntegral ψ (arrayEventLikelihood ℓ s) → ∀ {r : ℝ}, 0 < r →
    (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s))⁻¹ * stateWeightedIntegral ψ
      (fun x => arrayEventLikelihood ℓ s x*
        (Coulomb.localCount {z : Position | α*r < ‖z‖ ∧ ‖z‖ < β*r} (flattenConfiguration n x))^2) ≤
    C*(Coulomb.screenMass (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*
      (1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5) r)^2 := by
  obtain ⟨C,hC,hbound⟩ := Coulomb.atomic_annular_second_moment hα hαβ
  refine ⟨C,hC,?_⟩
  intro H _ n Z hZ ψ g hd hn hmin E D₀ hE hbase hD ℓ hℓ s hs hsym hp r hr
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase ℓ hℓ hs hsym hp
  have hb := hbound (Coulomb.atom Z hZ) (by intro i; rfl) u hu hum hE hue
    (observationEventOffset_nonneg hd hn hD ℓ hs hp) hr
  change Coulomb.potentialForm (fun x => (Coulomb.localCount _ x)^2) u ≤ _ at hb
  rw [hlaw] at hb
  exact hb

theorem atomic_arrayEvent_raw_field {H : Type*} [Fintype H] {n : ℕ}
    (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n),
      FormDomain χ h → normSquared χ=1 → energy Z ψ g ≤ energy Z χ h)
    {E D₀ : ℝ} (hE : (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g ≤ E+D₀) (hD : 0 ≤ D₀)
    (ℓ : H → ℝ) (hℓ : ∀ h, 0 < ℓ h)
    {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (hsym : ∀ (p : Equiv.Perm (Fin n)) y, permuteObservationArray p y∈s ↔ y∈s)
    (hp : 0 < stateWeightedIntegral ψ (arrayEventLikelihood ℓ s))
    {y : Position} (hy : y≠0) :
    max ((stateWeightedIntegral ψ (arrayEventLikelihood ℓ s))⁻¹ * stateWeightedIntegral ψ
      (fun x => arrayEventLikelihood ℓ s x *
        Coulomb.rawSignedField (Coulomb.attraction (Coulomb.atom Z hZ) y)
          {z | 40*Coulomb.atomicCellScale y ≤ ‖z-y‖} y (flattenConfiguration n x))) 0 ≤
    2*Coulomb.atomicBudgetRecursionC^2*Coulomb.screenFieldUnit
      (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*
      (1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5)
      Coulomb.atomicCountConstant (Coulomb.atomicCellScale y) := by
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase ℓ hℓ hs hsym hp
  have hb := Coulomb.atomic_expected_raw_field_bound (Coulomb.atom Z hZ) (by intro i; rfl)
    u hu hum hE hue (observationEventOffset_nonneg hd hn hD ℓ hs hp) hy
  have hA : MeasurableSet {z : Position | 40*Coulomb.atomicCellScale y ≤ ‖z-y‖} :=
    (isClosed_le continuous_const (by fun_prop)).measurableSet
  rw [←hlaw,Coulomb.potentialForm_rawSignedField u _ hA
    y (mul_pos (by norm_num) (Coulomb.atomicCellScale_pos hy)) (fun _ h => h),hum,mul_one]
  exact hb
end NeutralAtom
end

end
end

end OAI
