import OAI.Analysis.CircleDomains.Sobolev.EnergyTransportIntegrability
import OAI.Analysis.CircleDomains.Sobolev.ComplexRealEnergy
import OAI.Analysis.CircleDomains.Transfer.TransportedTerminalBranches

namespace OAI

/-!
# Finite-chart energy of the actual transported real function

Both integrability and the energy identity follow from the Jacobian
formula. Restriction to the bounded disk used by line payment only
decreases this energy.
-/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem transported_sphereRealFunction_eq
    (w : (ℝ × ℝ) → ℝ) (fi : Sphere → Sphere) :
    (sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere) =
      (w ∘ sphereRealMap fi) ∘ Complex.equivRealProdCLM := by
  funext z
  simp only [sphereRealFunction, sphereRealMap, comp_apply,
    ContinuousLinearEquiv.symm_apply_apply]

theorem transported_real_energy
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (w : (ℝ × ℝ) → ℝ) (hw : ContDiffOn ℝ ∞ w (realChartDomain U))
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p)
    (hg : ∀ x ∈ realChartDomain U, (g x).PosDef)
    (hi : IntegrableOn (gradientEnergy w g) (realChartDomain U)) :
    ContDiffOn ℝ 1 ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))
        (((↑) : ℂ → Sphere) ⁻¹' V) ∧
      IntegrableOn (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
        (((↑) : ℂ → Sphere) ⁻¹' V) ∧
      (∫ z in (((↑) : ℂ → Sphere) ⁻¹' V),
        euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) z) =
        ∫ x in realChartDomain U, gradientEnergy w g x := by
  have hO := isOpen_realChartDomain hU
  have hW := isOpen_realChartDomain hV
  have himage := (heq.real_bijOn hUinf hfix).image_eq
  obtain ⟨_, hsmooth, _⟩ := transported_real_coordinate heq hV hUinf hfix hO
    (Subset.refl _) w hw
  rw [himage] at hsmooth
  have hi' := (integrable_transported_real_coordinate_iff heq hV hUinf hfix
    hO (Subset.refl _) w hw hO.measurableSet (Subset.refl _) hf hg).mpr hi
  rw [himage] at hi'
  have hdomain : Complex.equivRealProdCLM ⁻¹' realChartDomain V =
      ((↑) : ℂ → Sphere) ⁻¹' V := by
    ext z
    simp only [mem_preimage, realChartDomain, ContinuousLinearEquiv.symm_apply_apply]
  have hsmooth1 : ContDiffOn ℝ 1 (w ∘ sphereRealMap fi) (realChartDomain V) :=
    hsmooth.of_le (by norm_num)
  obtain ⟨hci, hce⟩ := real_gradient_energy_in_complex_coordinates hW hW.measurableSet
    (Subset.refl _) hsmooth1 hi'
  rw [hdomain, ← transported_sphereRealFunction_eq] at hci hce
  refine ⟨?_, hci, hce.trans ?_⟩
  · rw [transported_sphereRealFunction_eq, ← hdomain]
    exact hsmooth1.comp Complex.equivRealProdCLM.contDiff.contDiffOn (fun _ hz => hz)
  · have hid := integral_transported_real_coordinate heq hV hUinf hfix hO
      (Subset.refl _) w hw hO.measurableSet (Subset.refl _) hf hg
    rwa [himage] at hid

theorem transported_real_energy_on_disk_le
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (w : (ℝ × ℝ) → ℝ) (hw : ContDiffOn ℝ ∞ w (realChartDomain U))
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p)
    (hg : ∀ x ∈ realChartDomain U, (g x).PosDef)
    (hi : IntegrableOn (gradientEnergy w g) (realChartDomain U)) (L : ℝ) :
    IntegrableOn (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
        ((((↑) : ℂ → Sphere) ⁻¹' V) ∩ Metric.closedBall 0 L) ∧
      (∫ z in (((↑) : ℂ → Sphere) ⁻¹' V) ∩ Metric.closedBall 0 L,
        euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) z) ≤
        ∫ x in realChartDomain U, gradientEnergy w g x := by
  obtain ⟨_, hfull, he⟩ := transported_real_energy heq hU hV hUinf hfix w hw hf hg hi
  refine ⟨hfull.mono_set inter_subset_left, ?_⟩
  rw [← he]
  exact setIntegral_mono_set hfull
    (ae_of_all _ (fun z => euclideanGradientEnergy_nonneg _ z))
    (Eventually.of_forall fun _ hz => hz.1)

end CircleDomainRigidity

end

end OAI
