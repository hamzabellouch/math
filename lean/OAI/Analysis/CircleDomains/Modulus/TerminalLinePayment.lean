import OAI.Analysis.CircleDomains.Topology.FiniteTerminalDisks
import OAI.Analysis.CircleDomains.Modulus.FiniteCircleLinePayment

namespace OAI

/-!
# Parallel-line payment for an actual normalized finite model

The round holes are taken from the model's terminal assignment. Their
cluster costs are derived from the real function on the physical terminal
boundaries. This joins line payment to the finite-transfer construction.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem TerminalComponentAssignment.parallel_line_payment
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
      ((((↑) : ℂ → Sphere) ⁻¹' V) ∩ closedBall 0 L))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (horizontalLine y s : Sphere) ∈ V ∧ (horizontalLine y t : Sphere) ∈ V ∧
      horizontalLine y s ∈ closedBall 0 L ∧ horizontalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction w (fi (horizontalLine y s)) = 0 ∧
      sphereRealFunction w (fi (horizontalLine y t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in (((↑) : ℂ → Sphere) ⁻¹' V) ∩ closedBall 0 L,
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
      ((⋃ j, closedBall (c j) (r j))ᶜ ∩ closedBall 0 L) := by simpa only [hU] using henergy
  rw [hU]
  apply parallel_line_payment_on_finite_disk_complement_square_norm c r A hr
    (fun _ => Metric.diam_nonneg) hL hd hsub hv' he' hcl hJ
  intro y hy
  obtain ⟨s, t, hst, hsV, htV, hsB, htB, hs0, ht1⟩ := hcross y hy
  refine ⟨s, t, hst, ?_, ?_, hsB, htB, hs0, ht1⟩
  · change horizontalLine y s ∈ (⋃ j, closedBall (c j) (r j))ᶜ
    rw [← hU]
    exact hsV
  · change horizontalLine y t ∈ (⋃ j, closedBall (c j) (r j))ᶜ
    rw [← hU]
    exact htV

end CircleDomainRigidity

end

end OAI
