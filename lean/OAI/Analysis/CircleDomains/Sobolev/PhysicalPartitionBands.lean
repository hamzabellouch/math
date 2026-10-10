import OAI.Analysis.CircleDomains.Topology.QuotientFinitePlane
import OAI.Analysis.CircleDomains.Topology.QuotientSamplingBands
import OAI.Analysis.CircleDomains.Sobolev.LocalSmoothPartition

namespace OAI

/-! The quotient-band consequence of a physical positive sampling partition. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem physical_partition_band_inclusion
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain)
    (π : Sphere → X) (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hinf : OnePoint.infty ∈ d.physicalDomain) (hinfB : π OnePoint.infty ∉ d.dust)
    {ι : Type*} (ρ : OpenPlanePartition (physicalPlaneOpens d.physicalDomain hG) ι)
    (a b c e : ι → ℝ)
    (hphys : ∀j z, z ∈ closedComplexRectangle (a j) (b j) (c j) (e j) →
      (z : Sphere) ∈ d.physicalDomain)
    (hsub : ∀j, tsupport (ρ.weight j) ⊆
      euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j)))
    (hpair : ∀j x, x ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)) →
      ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)),
        dist (π (planeSphere y)) (π (planeSphere x)) ≤ Metric.infDist (π (planeSphere x)) d.dust)
    (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1) (w : EuclideanPlane → ℝ)
    (hinter : ∀x ∈ physicalPlaneDomain d.physicalDomain, ∀r s : ℝ,
      (∀j, ρ.weight j x ≠ 0 → ∀y ∈
        euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j)),
        u (π (planeSphere y)) ∈ Icc r s) → w x ∈ Icc r s) :
    ∀s ∈ d.dust, s ∈ closure d.quotientDomain →
      liminf u (𝓝[d.quotientDomain] s) ≤
        liminf (quotientPlaneRepresentative d w) (𝓝[d.quotientDomain] s) ∧
      limsup (quotientPlaneRepresentative d w) (𝓝[d.quotientDomain] s) ≤
        limsup u (𝓝[d.quotientDomain] s) := by
  let Ω := physicalPlaneOpens d.physicalDomain hG
  let q : EuclideanPlane → X := π ∘ planeSphere
  intro s hs hscl
  have hsne : s ≠ π OnePoint.infty := by
    intro heq
    exact hinfB (heq ▸ hs)
  let U := d.quotientDomain \ {π OnePoint.infty}
  have hnhds : 𝓝[U] s = 𝓝[d.quotientDomain] s :=
    hsne.nhdsWithin_sdiff_singleton d.quotientDomain
  have hsclU : s ∈ closure U := by
    rw [mem_closure_iff_nhdsWithin_neBot, hnhds]
    exact mem_closure_iff_nhdsWithin_neBot.mp hscl
  let W : ι → Set EuclideanPlane := fun j =>
    euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j))
  have hclosed (j : ι) : W j ⊆
      euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)) := by
    intro x hx
    exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, ⟨hx.2.1.le, hx.2.2.le⟩⟩
  have hWO (j : ι) : W j ⊆ Ω := by
    intro x hx
    exact hphys j _ (mk_mem_closedComplexRectangle (hclosed j hx).1 (hclosed j hx).2)
  have hbound := quotient_sampling_band_inclusion (Ω : Set EuclideanPlane) U d.dust q
    ρ.weight W u (quotientPlaneRepresentative d w) w
    (quotient_finite_plane_mapsTo d π he hinf) (quotient_finite_plane_covers d π he)
    (fun x hx => quotientPlaneRepresentative_plane d w π he hx) hWO
    (by
      intro x hx j hj y hy
      exact hpair j x (hclosed j (hsub j (subset_tsupport (ρ.weight j) hj))) y (hclosed j hy))
    hinter hu hs hsclU
  simpa only [hnhds] using hbound


end CircleDomainRigidity

end

end OAI
