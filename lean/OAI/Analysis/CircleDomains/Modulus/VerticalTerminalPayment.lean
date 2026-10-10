import OAI.Analysis.CircleDomains.Topology.FiniteTerminalDisks
import OAI.Analysis.CircleDomains.Modulus.VerticalCirclePayment
import OAI.Analysis.CircleDomains.Sobolev.TransportedRealEnergy

namespace OAI

/-!
# Vertical-line payment for an actual normalized finite model

The round holes are taken from the model's terminal assignment. Their
cluster costs are derived from the real function on the physical terminal
boundaries. This joins line payment to the finite-transfer construction.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem TerminalComponentAssignment.vertical_line_payment
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsCircleDomain V) (hinf : OnePoint.infty ∈ V)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : Vᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    (w : (ℝ × ℝ) → ℝ) {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O) (hw : ContinuousOn w O)
    (hv : ContDiffOn ℝ 1 ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))
      (((↑) : ℂ → Sphere) ⁻¹' V))
    (henergy : IntegrableOn
      (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' V))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (verticalLine y s : Sphere) ∈ V ∧ (verticalLine y t : Sphere) ∈ V ∧
      verticalLine y s ∈ closedBall 0 L ∧ verticalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction w (fi (verticalLine y s)) = 0 ∧
      sphereRealFunction w (fi (verticalLine y t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in (((↑) : ℂ → Sphere) ⁻¹' V),
        euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) z) +
      2 * L * Real.sqrt (∑ i, Metric.diam (w '' frontier (realJordanInterior (T i))) ^ 2) := by
  obtain ⟨c, r, hr, he, hd, hU⟩ := a.exists_disk_coordinates hV hinf
  let A : I → ℝ := fun i => Metric.diam (w '' frontier (realJordanInterior (T i)))
  have hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall (0 : ℂ) L :=
    fun i => terminal_disk_subset_bound (he i) hbound
  have hcl : ∀ i p q u v, p ∈ closedBall (c i) (r i) → q ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p)
        ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) →
      MapClusterPt v (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] q)
        ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) → |v - u| ≤ A i := by
    intro i p q u v hp hq hu hv
    apply a.real_planar_cluster_gap_le hf i w hO (hTO i) hw
    · rw [he i]
      exact mem_image_of_mem _ hp
    · rw [he i]
      exact mem_image_of_mem _ hq
    · simpa only [hU] using hu
    · simpa only [hU] using hv
  have hv' : ContDiffOn ℝ 1 ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))
      (⋃ j, closedBall (c j) (r j))ᶜ := by simpa only [hU] using hv
  have he' : IntegrableOn
      (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
      ((⋃ j, closedBall (c j) (r j))ᶜ) := by simpa only [hU] using henergy
  rw [hU]
  apply vertical_line_payment_on_finite_disk_complement c r A hr
    (fun _ => Metric.diam_nonneg) hL hd hsub hv' he' hcl hJ
  intro y hy
  obtain ⟨s, t, hst, hsV, htV, hsB, htB, hs0, ht1⟩ := hcross y hy
  refine ⟨s, t, hst, ?_, ?_, hsB, htB, hs0, ht1⟩
  · change verticalLine y s ∈ (⋃ j, closedBall (c j) (r j))ᶜ
    rw [← hU]
    exact hsV
  · change verticalLine y t ∈ (⋃ j, closedBall (c j) (r j))ᶜ
    rw [← hU]
    exact htV

theorem TerminalComponentAssignment.vertical_line_payment_source_energy
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (heq : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsCircleDomain V) (hinf : OnePoint.infty ∈ openCompletedRegion T)
    (hfix : f OnePoint.infty = OnePoint.infty)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : Vᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    (w : (ℝ × ℝ) → ℝ)
    (hw : ContDiffOn ℝ ∞ w (realChartDomain (openCompletedRegion T)))
    {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O) (hwO : ContinuousOn w O)
    {g : (ℝ × ℝ) → PlanarMetric}
    (hmetric : ∀ p ∈ openCompletedRegion T, IsMetricConformalAt g f p)
    (hg : ∀ x ∈ realChartDomain (openCompletedRegion T), (g x).PosDef)
    (hi : IntegrableOn (gradientEnergy w g) (realChartDomain (openCompletedRegion T)))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ x ∈ J, ∃ s t : ℝ, s < t ∧
      (verticalLine x s : Sphere) ∈ V ∧ (verticalLine x t : Sphere) ∈ V ∧
      verticalLine x s ∈ closedBall 0 L ∧ verticalLine x t ∈ closedBall 0 L ∧
      sphereRealFunction w (fi (verticalLine x s)) = 0 ∧
      sphereRealFunction w (fi (verticalLine x t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ x in realChartDomain (openCompletedRegion T), gradientEnergy w g x) +
      2 * L * Real.sqrt (∑ i, Metric.diam (w '' frontier (realJordanInterior (T i))) ^ 2) := by
  obtain ⟨hv, hfull, he⟩ := transported_real_energy heq (isOpen_openCompletedRegion T)
    hV.1 hinf hfix w hw hmetric hg hi
  have hp := a.vertical_line_payment heq hV (heq.infty_mem_target hinf hfix)
    hL hbound w hO hTO hwO hv hfull hJ hcross
  rwa [he] at hp

end CircleDomainRigidity

end

end OAI
