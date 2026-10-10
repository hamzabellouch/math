import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.MasterPosteriorPotential
import OAI.Analysis.CoulombIonization.Variational.OriginalKernelEvent

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma jointMasterPosterior_potential_setIntegral {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) :
    (∫ z in A, tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
      ∂physicalObservationLaw μ K) =
      ∫ z in A, ∑ i, tfPotential (masterKernel c₁ r₀ s g (z.1 i)) y ∂physicalObservationLaw μ K := by
  rw [integral_congr_ae (ae_restrict_of_ae
    (jointMasterPosterior_potential_eq_kernel μ ell j y hi he hc hr hs hg hcg hgn hrad hgs))]
  exact kernelPosteriorTest_setIntegral μ ell j (masterKernel_pole_measurable hc hr hs hg.continuous y)
    (master_configuration_potential_integrable μ y hi he hc hr hs hg hcg hgn hrad hgs) hA

theorem master_potential_event_loss {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) :
    0 ≤ (∫ z in A, rawPotential y z.1 ∂physicalObservationLaw μ K)-
      (∫ z in A, tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
        ∂physicalObservationLaw μ K) ∧
    (∫ z in A, rawPotential y z.1 ∂physicalObservationLaw μ K)-
      (∫ z in A, tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
        ∂physicalObservationLaw μ K) ≤
      ∫ z in A, rawLocalPotential y (2*masterWidth c₁ r₀ s y) z.1 ∂physicalObservationLaw μ K := by
  let v : Space → ℝ := fun x => 1/‖x-y‖
  let l : Space → ℝ := (ball y (2*masterWidth c₁ r₀ s y)).indicator v
  have hv : Measurable v := by fun_prop
  have hl : Measurable l := hv.indicator measurableSet_ball
  have hli : Integrable (fun x : Configuration N => ∑ i, l (x i)) μ := by
    have heq : (fun x : Configuration N => ∑ i, l (x i)) =
        rawLocalPotential y (2*masterWidth c₁ r₀ s y) := by
      funext x
      exact (rawLocalPotential_eq_indicator y _ x).symm
    rw [heq]
    exact rawLocalPotential_integrable_of_raw y _ hi
  have hvr := (kernelPosteriorTest_integrable μ ell j hv hi).integrableOn (s := A)
  have hlr := (kernelPosteriorTest_integrable μ ell j hl hli).integrableOn (s := A)
  have hpr := (jointMasterPosterior_potential_integrable μ ell j y hi he hc hr hs hg hcg hgn hrad hgs).integrableOn (s := A)
  have hpoint := ae_restrict_of_ae (s := A) (jointMasterPosterior_potential_loss μ ell j y hi he
    hc hcL hr hs hs1 hg hcg hgn hrad hgs)
  have hn := integral_nonneg_of_ae (hpoint.mono fun _ h => h.1)
  have hb := integral_mono_ae (hvr.sub hpr) hlr (hpoint.mono fun _ h => h.2)
  simp only [Pi.sub_apply] at hb
  rw [integral_sub hvr hpr,kernelPosteriorTest_setIntegral μ ell j hv hi hA] at hn hb
  rw [kernelPosteriorTest_setIntegral μ ell j hl hli hA] at hb
  simpa only [rawPotential,rawLocalPotential_eq_indicator] using And.intro hn hb

end CoulombAtom

end

end OAI
