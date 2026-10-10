import OAI.Analysis.CircleDomains.Sobolev.PhysicalSamplingPartition
import OAI.Analysis.CircleDomains.Sobolev.RefinedShrinkingRectanglePartition

namespace OAI

/-! Refined sampling for the actual physical quotient, with plateau neighborhoods. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem exists_refined_physical_sampling_partition
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → X) (hπ : Continuous π)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hne : d.dust.Nonempty)
    (N : physicalPlaneOpens d.physicalDomain hG → Set EuclideanPlane)
    (hN : ∀x, IsOpen (N x)) (hxN : ∀x, x.val ∈ N x) :
    ∃ (ι : Type) (_ : Countable ι)
      (ρ : OpenPlanePartition (physicalPlaneOpens d.physicalDomain hG) ι)
      (center : ι → physicalPlaneOpens d.physicalDomain hG) (a b c e : ι → ℝ),
      (∀j, a j < b j ∧ c j < e j) ∧
      (∀j z, z ∈ closedComplexRectangle (a j) (b j) (c j) (e j) →
        (z : Sphere) ∈ d.physicalDomain) ∧
      (∀j, tsupport (ρ.weight j) ⊆
        euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j))) ∧
      (∀j x, x ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)) →
        ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)),
          dist (π (planeSphere y)) (π (planeSphere x)) ≤ Metric.infDist (π (planeSphere x)) d.dust) ∧
      (∀j x, x ∈ closedComplexRectangle (a j) (b j) (c j) (e j) →
        ∀y ∈ closedComplexRectangle (a j) (b j) (c j) (e j), dist x y ≤ 1) ∧
      (∀j, euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)) ⊆ N (center j)) := by
  let Ω := physicalPlaneOpens d.physicalDomain hG
  let q : EuclideanPlane → X := π ∘ planeSphere
  have hq : ContinuousOn q Ω := (hπ.comp continuous_planeSphere).continuousOn
  have havoid (x : EuclideanPlane) (hx : x ∈ Ω) : q x ∉ d.dust := by
    have hp : planeSphere x ∈ d.physicalDomain := hx
    have hu : q x ∈ d.quotientDomain := by
      change π (planeSphere x) ∈ d.quotientDomain
      rw [← he ⟨planeSphere x, hp⟩]
      exact (d.domainEquiv ⟨planeSphere x, hp⟩).property
    exact fun hb => Set.disjoint_left.mp hdisj hu hb
  obtain ⟨ι, hι, ρ, center, a, b, c, e, hlt, hrect, hsub, hpair, hdiam⟩ :=
    exists_small_shrinking_partition_refining_neighborhoods Ω q hq d.dust hB hne havoid N hN hxN
  refine ⟨ι, hι, ρ, center, a, b, c, e, hlt, ?_, hsub, hpair, ?_, ?_⟩
  · intro j
    exact physical_closed_rectangle_of_coordinate_subset ((hrect j).trans inter_subset_left)
  · intro j
    exact complex_rectangle_diameter_of_coordinate_diameter (hdiam j)

  · intro j
    exact (hrect j).trans inter_subset_right

end CircleDomainRigidity

end

end OAI
