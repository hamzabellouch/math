import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.MasterJointPosterior
import OAI.Analysis.CoulombIonization.Variational.MasterKernelFubini

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma jointMasterPosterior_potential_eq_kernel {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    (fun z => tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y) =ᵐ[
      physicalObservationLaw μ K] fun z => kernelPosteriorTest μ ell j
        (fun x => tfPotential (masterKernel c₁ r₀ s g x) y) (originalDatum ell j z) := by
  filter_upwards [originalRawKernel_integrable μ ell j (rawPotential_measurable y) hi,
    originalRawKernel_ae μ ell j he] with z hz hze
  exact master_configuration_potential_fubini _ y hz hze hc hr hs hg hcg hgn hrad hgs

lemma jointMasterPosterior_potential_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun z => tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y)
      (physicalObservationLaw μ K) :=
  (kernelPosteriorTest_integrable μ ell j (masterKernel_pole_measurable hc hr hs hg.continuous y)
    (master_configuration_potential_integrable μ y hi he hc hr hs hg hcg hgn hrad hgs)).congr
      (jointMasterPosterior_potential_eq_kernel μ ell j y hi he hc hr hs hg hcg hgn hrad hgs).symm

lemma jointMasterPosterior_potential_mean {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    (∫ z, tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
      ∂physicalObservationLaw μ K) = ∫ x, ∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y ∂μ := by
  rw [integral_congr_ae (jointMasterPosterior_potential_eq_kernel μ ell j y hi he hc hr hs hg hcg hgn hrad hgs)]
  exact kernelPosteriorTest_mean μ ell j (masterKernel_pole_measurable hc hr hs hg.continuous y)
    (master_configuration_potential_integrable μ y hi he hc hr hs hg hcg hgn hrad hgs)

theorem jointMasterPosterior_potential_loss {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      0 ≤ kernelPosteriorTest μ ell j (fun x => 1/‖x-y‖) (originalDatum ell j z)-
        tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y ∧
      kernelPosteriorTest μ ell j (fun x => 1/‖x-y‖) (originalDatum ell j z)-
        tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y ≤
      kernelPosteriorTest μ ell j ((ball y (2*masterWidth c₁ r₀ s y)).indicator (fun x => 1/‖x-y‖))
        (originalDatum ell j z) := by
  filter_upwards [originalRawKernel_integrable μ ell j (rawPotential_measurable y) hi,
    originalRawKernel_ae μ ell j he] with z hz hze
  unfold jointMasterPosterior kernelPosteriorTest
  simpa only [rawLocalPotential_eq_indicator,rawPotential] using
    (master_configuration_potential_loss (originalRawKernel μ ell j (originalDatum ell j z)) y hz hze
      hc hcL hr hs hs1 hg hcg hgn hrad hgs)

theorem quantum_master_potential_loss {N K : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    letI : IsFiniteMeasure (formRawLaw ψ) := formRawLaw_finite hψ
    0 ≤ (∫ x, rawPotential y x ∂formRawLaw ψ)-
      (∫ z, tfPotential (jointMasterPosterior (formRawLaw ψ) ell j c₁ r₀ s g (originalDatum ell j z)) y
        ∂physicalObservationLaw (formRawLaw ψ) K) ∧
    (∫ x, rawPotential y x ∂formRawLaw ψ)-
      (∫ z, tfPotential (jointMasterPosterior (formRawLaw ψ) ell j c₁ r₀ s g (originalDatum ell j z)) y
        ∂physicalObservationLaw (formRawLaw ψ) K) ≤
      ∫ x, rawLocalPotential y (2*masterWidth c₁ r₀ s y) x ∂formRawLaw ψ := by
  let : IsFiniteMeasure (formRawLaw ψ) := formRawLaw_finite hψ
  rw [jointMasterPosterior_potential_mean (formRawLaw ψ) ell j y (rawPotential_form_integrable hψ y)
    (formRawLaw_ae_no_poles ψ y) hc hr hs hg hcg hgn hrad hgs]
  rw [←master_configuration_potential_fubini (formRawLaw ψ) y (rawPotential_form_integrable hψ y)
    (formRawLaw_ae_no_poles ψ y) hc hr hs hg hcg hgn hrad hgs]
  exact master_configuration_potential_loss (formRawLaw ψ) y (rawPotential_form_integrable hψ y)
    (formRawLaw_ae_no_poles ψ y) hc hcL hr hs hs1 hg hcg hgn hrad hgs

end CoulombAtom

end

end OAI
