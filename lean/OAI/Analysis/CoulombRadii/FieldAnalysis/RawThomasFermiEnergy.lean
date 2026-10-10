import Mathlib
import OAI.Analysis.CoulombRadii.Packets.WindowCoulomb
import OAI.Analysis.CoulombRadii.Packets.FineKernelShiftCoulombIntegrable
import OAI.Analysis.CoulombRadii.Localization.DeletedLabels

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

def rawThomasFermiEnergy (Φ ρ : Space → ℝ) : ℝ :=
  thomasFermiCoefficient*(∫ y, ρ y^(5/3:ℝ)) - (∫ y, Φ y*ρ y) + coulombBilinear ρ ρ/2

lemma sliceExpectation_congr_ae {m k : ℕ} (ψ : H1Vector (m+k))
    {f g : Spins m → Configuration m → ℝ} (h : ∀ s, f s =ᵐ[volume] g s) :
    sliceExpectation ψ f = sliceExpectation ψ g := by
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae
  exact (h s).mono fun x hx => congrArg (mass (ψ.coreSlice s x)*·) hx

lemma discreteFineTF_eq_raw {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m)) (s : Spins m) (x : Configuration m)
    {A : Set Space} (hu : SpatiallySupported (ψ.coreSlice s x).normalized A)
    (hnuc : ∀ j i, i ∈ r x → Real.sqrt 3*b ≤ ‖S.position j-position x i‖)
    (hcore : ∀ z ∈ A, ∀ i ∈ r x, Real.sqrt 3*b ≤ ‖z-position x i‖) :
    discreteFineTF S ψ b r s x = rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized)
      (retainedFineDensity b (r x) (position x)) := by
  unfold discreteFineTF rawThomasFermiEnergy retainedFinePower retainedFineCoulomb
  rw [coreScreenedField_retainedFine_eq S (ψ.coreSlice s x).normalized hu hb (r x) (position x) hnuc hcore]
  ring

theorem conditional_source_free_lower {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (hψ : ∀ (s : Spins k) (p : Equiv.Perm (Fin m)) (t : Spins m),
      ∀ᵐ z, ψ.value (outerAppend s t ∘ outerPerm k p) (permute (outerPerm k p) z) =
        (((outerPerm k p).sign : ℤ) : ℂ)*ψ.value (outerAppend s t) z)
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (F : Spins m → Configuration m → ℝ)
    (hFi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*(F s x*(deletedLabels r x).card)))
    (hcap : ∀ s, ∀ᵐ x, ∀ i ∈ deletedLabels r x,
      coreScreenedField S (ψ.coreSlice s x).normalized (position x i) ≤ F s x)
    (A : Spins m → Configuration m → Set Space)
    (hsupport : ∀ s, ∀ᵐ x, SpatiallySupported (ψ.coreSlice s x).normalized (A s x))
    (hnuc : ∀ s : Spins m, ∀ᵐ x, ∀ j i, i ∈ r x → Real.sqrt 3*b ≤ ‖S.position j-position x i‖)
    (hcore : ∀ s, ∀ᵐ x, ∀ z ∈ A s x, ∀ i ∈ r x, Real.sqrt 3*b ≤ ‖z-position x i‖) :
    sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized +
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized)
        (retainedFineDensity b (r x) (position x))) -
      sliceExpectation ψ (fun s x => F s x*(deletedLabels r x).card) - fineLocalizationError m b*mass ψ ≤ form S ψ := by
  have he : sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized + discreteFineTF S ψ b r s x) =
      sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized +
        rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized)
          (retainedFineDensity b (r x) (position x))) := by
    apply sliceExpectation_congr_ae
    intro s
    filter_upwards [hsupport s, hnuc s, hcore s] with x hs hn hc
    rw [discreteFineTF_eq_raw S ψ hb r s x hs hn hc]
  rw [←he]
  exact conditional_fine_lower S ψ hψ hb r hr F hFi hcap

lemma source_free_trial_raw {M k : ℕ} (S : Nuclei M) (u : H1Vector k)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hR : 0 < R) (hgs : ∀ y, R < ‖y‖ → g y = 0)
    (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (ht : Integrable (fun y => ρ y^(5/3:ℝ)))
    (K A : Set Space) (hK : IsCompact K) (hA : IsClosed A)
    (hs : ∀ y, y ∉ K → ρ y = 0) (hsu : SpatiallySupported u A)
    (hsep : Disjoint A (K+tsupport (g : Space → ℝ)))
    (hcore : ∀ a ∈ A, ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖)
    (hnuc : ∀ j y, ρ y ≠ 0 → R ≤ ‖S.position j-y‖) :
    unrestrictedFormBottom S ≤ ((form S u+rawThomasFermiEnergy (coreScreenedField S u) ρ+
      (1/2:ℝ)*(∫ y, ρ y)*(∑ b : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single b 1))^2) : ℝ) : EReal) := by
  have H := source_free_trial_in_hole S u hu hmu g hg hgc hrad hR hgs ρ hp hm ht K A hK hA hs hsu hsep hcore hnuc
  convert H using 1
  congr 1
  have he : coulombBilinear ρ ρ =
      ∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2) := by
    unfold coulombBilinear
    apply integral_congr_ae; exact Eventually.of_forall (fun _ => by ring)
  unfold rawThomasFermiEnergy
  rw [he]
  unfold thomasFermiCoefficient thomasFermiKineticConstant
  ring

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

def SourceFreeHoleDensity {M k : ℕ} (S : Nuclei M) (u : H1Vector k)
    (g : 𝓢(Space,ℝ)) (R : ℝ) (ρ : Space → ℝ) (K A : Set Space) : Prop :=
  (∀ y, 0 ≤ ρ y) ∧ Measurable ρ ∧ Integrable (fun y => ρ y^(5/3:ℝ)) ∧
  IsCompact K ∧ IsClosed A ∧ (∀ y, y ∉ K → ρ y=0) ∧ SpatiallySupported u A ∧
  Disjoint A (K+tsupport (g : Space → ℝ)) ∧
  (∀ a ∈ A, ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖) ∧
  (∀ j y, ρ y ≠ 0 → R ≤ ‖S.position j-y‖)

def packetKineticError (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) : ℝ :=
  (1/2:ℝ)*(∫ y, ρ y)*(∑ b : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single b 1))^2)

lemma source_free_trial_from_density {M k : ℕ} (S : Nuclei M) (u : H1Vector k)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hR : 0 < R) (hgs : ∀ y, R < ‖y‖ → g y = 0)
    (ρ : Space → ℝ) (K A : Set Space) (hρ : SourceFreeHoleDensity S u g R ρ K A) :
    unrestrictedFormBottom S ≤ ((form S u+rawThomasFermiEnergy (coreScreenedField S u) ρ+
      packetKineticError g ρ : ℝ) : EReal) := by
  rcases hρ with ⟨hp,hm,ht,hK,hA,hs,hsu,hsep,hcore,hnuc⟩
  exact source_free_trial_raw S u hu hmu g hg hgc hrad hR hgs ρ hp hm ht K A hK hA hs hsu hsep hcore hnuc

lemma sliceExpectation_number {m k : ℕ} (ψ : H1Vector (m+k)) (E : ℝ) :
    sliceExpectation ψ (fun _ _ => E) = E*mass ψ := by
  simp only [sliceExpectation, mul_comm (mass _) E, integral_const_mul, ←Finset.mul_sum]
  rw [integral_mass_coreSlice]

theorem conditional_source_free_upper {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (hcoreAnti : ∀ s, ∀ᵐ x, Antisymmetric (ψ.coreSlice s x))
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hR : 0 < R) (hgs : ∀ y, R < ‖y‖ → g y = 0)
    (ρ : Spins m → Configuration m → Space → ℝ)
    (K A : Spins m → Configuration m → Set Space)
    (hρ : ∀ s, ∀ᵐ x, SourceFreeHoleDensity S (ψ.coreSlice s x).normalized g R (ρ s x) (K s x) (A s x))
    (hTi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)))
    (hKi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*packetKineticError g (ρ s x)))
    {E : ℝ} (hE : (E : EReal) ≤ unrestrictedFormBottom S) :
    E*mass ψ ≤ sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized+
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)) +
      sliceExpectation ψ (fun s x => packetKineticError g (ρ s x)) := by
  have hCi := normalized_coreForm_weight_integrable S ψ
  have hCT (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(form S (ψ.coreSlice s x).normalized+
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x))) := by
    apply ((hCi s).add (hTi s)).congr
    exact Eventually.of_forall (fun x => (mul_add ..).symm)
  rw [←sliceExpectation_add ψ _ _ hCT hKi]
  rw [←sliceExpectation_number ψ E]
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono_ae
    (by simpa only [mul_comm (mass _) E] using (mass_coreSlice_integrable ψ s).const_mul E)
    (by
      apply ((hCT s).add (hKi s)).congr
      exact Eventually.of_forall (fun x => (mul_add ..).symm))
  filter_upwards [hcoreAnti s, hρ s] with x hx hρx
  by_cases hz : mass (ψ.coreSlice s x)=0
  · simp [hz]
  · have hp : 0 < mass (ψ.coreSlice s x) := lt_of_le_of_ne (mass_nonneg _) (Ne.symm hz)
    have H := source_free_trial_from_density S (ψ.coreSlice s x).normalized hx.normalized
      (mass_normalized _ hp) g hg hgc hrad hR hgs (ρ s x) (K s x) (A s x) hρx
    have HE : E ≤ form S (ψ.coreSlice s x).normalized +
        rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)+packetKineticError g (ρ s x) :=
      EReal.coe_le_coe_iff.mp (hE.trans H)
    exact mul_le_mul_of_nonneg_left HE hp.le

theorem source_free_patch_comparison {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (houterAnti : ∀ (s : Spins k) (p : Equiv.Perm (Fin m)) (t : Spins m),
      ∀ᵐ z, ψ.value (outerAppend s t ∘ outerPerm k p) (permute (outerPerm k p) z) =
        (((outerPerm k p).sign : ℤ) : ℂ)*ψ.value (outerAppend s t) z)
    (hcoreAnti : ∀ s, ∀ᵐ x, Antisymmetric (ψ.coreSlice s x))
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (F : Spins m → Configuration m → ℝ)
    (hFi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*(F s x*(deletedLabels r x).card)))
    (hcap : ∀ s, ∀ᵐ x, ∀ i ∈ deletedLabels r x,
      coreScreenedField S (ψ.coreSlice s x).normalized (position x i) ≤ F s x)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hR : 0 < R) (hgs : ∀ y, R < ‖y‖ → g y = 0)
    (ρ : Spins m → Configuration m → Space → ℝ)
    (K A : Spins m → Configuration m → Set Space)
    (hρ : ∀ s, ∀ᵐ x, SourceFreeHoleDensity S (ψ.coreSlice s x).normalized g R (ρ s x) (K s x) (A s x))
    (hnuc : ∀ s : Spins m, ∀ᵐ x, ∀ j i, i ∈ r x → Real.sqrt 3*b ≤ ‖S.position j-position x i‖)
    (hcore : ∀ s, ∀ᵐ x, ∀ z ∈ A s x, ∀ i ∈ r x, Real.sqrt 3*b ≤ ‖z-position x i‖)
    (hTi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)))
    (hKi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*packetKineticError g (ρ s x)))
    {E : ℝ} (hE : (E : EReal) ≤ unrestrictedFormBottom S) :
    sliceExpectation ψ (fun s x =>
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (retainedFineDensity b (r x) (position x)) -
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)) ≤
      form S ψ-E*mass ψ + sliceExpectation ψ (fun s x => packetKineticError g (ρ s x)) +
      sliceExpectation ψ (fun s x => F s x*(deletedLabels r x).card) +fineLocalizationError m b*mass ψ := by
  have hs : ∀ s, ∀ᵐ x, SpatiallySupported (ψ.coreSlice s x).normalized (A s x) := by
    intro s; exact (hρ s).mono fun x h => h.2.2.2.2.2.2.1
  have hσeq (s : Spins m) : discreteFineTF S ψ b r s =ᵐ[volume]
      (fun x => rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized)
        (retainedFineDensity b (r x) (position x))) := by
    filter_upwards [hs s, hnuc s, hcore s] with x hx hy hz
    exact discreteFineTF_eq_raw S ψ hb r s x hx hy hz
  have hσi (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (retainedFineDensity b (r x) (position x))) := by
    apply (discreteFineTF_weight_integrable S ψ hb r hr s).congr
    exact (hσeq s).mono fun x hx => congrArg (mass (ψ.coreSlice s x)*·) hx
  have HL := conditional_source_free_lower S ψ houterAnti hb r hr F hFi hcap A hs hnuc hcore
  have HU := conditional_source_free_upper S ψ hcoreAnti g hg hgc hrad hR hgs ρ K A hρ hTi hKi hE
  rw [sliceExpectation_add ψ _ _ (normalized_coreForm_weight_integrable S ψ) hσi] at HL
  rw [sliceExpectation_add ψ _ _ (normalized_coreForm_weight_integrable S ψ) hTi] at HU
  rw [sliceExpectation_sub ψ _ _ hσi hTi]
  linarith
end Coulomb

end

end OAI
