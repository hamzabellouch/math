import OAI.Analysis.CircleDomains.Sobolev.PatchBandPreservation
import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates

namespace OAI

/-! Shrinking physical sampling patches preserve bands in the quotient
space, without requiring continuity of the boundary extension. -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {X ι : Type*} [MetricSpace X]

theorem quotient_sampling_eventual_bounds
    (Ω : Set EuclideanPlane) (U B : Set X) (q : EuclideanPlane → X)
    (weight : ι → EuclideanPlane → ℝ) (W : ι → Set EuclideanPlane)
    (u v : X → ℝ) (w : EuclideanPlane → ℝ)
    (hq : MapsTo q Ω U) (hcover : U ⊆ q '' Ω)
    (hvalue : ∀x ∈ Ω, v (q x) = w x)
    (hW : ∀j, W j ⊆ Ω)
    (hclose : ∀x ∈ Ω, ∀j, weight j x ≠ 0 → ∀y ∈ W j,
      dist (q y) (q x) ≤ infDist (q x) B)
    (hpreserve : ∀x ∈ Ω, ∀a b : ℝ,
      (∀j, weight j x ≠ 0 → ∀y ∈ W j, u (q y) ∈ Icc a b) → w x ∈ Icc a b)
    {s : X} (hs : s ∈ B) {a b : ℝ}
    (hu : ∀ᶠ y in 𝓝[U] s, u y ∈ Icc a b) :
    ∀ᶠ y in 𝓝[U] s, v y ∈ Icc a b := by
  obtain ⟨V, hV, hVU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hu
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hnear : ∀ᶠ z in 𝓝[U] s, dist z s < ε / 2 :=
    nhdsWithin_le_nhds (ball_mem_nhds s (half_pos hε))
  filter_upwards [self_mem_nhdsWithin, hnear] with z hz hzs
  obtain ⟨x, hx, rfl⟩ := hcover hz
  rw [hvalue x hx]
  apply hpreserve x hx a b
  intro j hj y hy
  apply hVU
  refine ⟨hball ?_, hq (hW j hy)⟩
  change dist (q y) s < ε
  have hdist := hclose x hx j hj y hy
  have hi : infDist (q x) B ≤ dist (q x) s := infDist_le_dist_of_mem hs
  linarith [dist_triangle (q y) (q x) s]

theorem quotient_sampling_band_inclusion
    (Ω : Set EuclideanPlane) (U B : Set X) (q : EuclideanPlane → X)
    (weight : ι → EuclideanPlane → ℝ) (W : ι → Set EuclideanPlane)
    (u v : X → ℝ) (w : EuclideanPlane → ℝ)
    (hq : MapsTo q Ω U) (hcover : U ⊆ q '' Ω)
    (hvalue : ∀x ∈ Ω, v (q x) = w x)
    (hW : ∀j, W j ⊆ Ω)
    (hclose : ∀x ∈ Ω, ∀j, weight j x ≠ 0 → ∀y ∈ W j,
      dist (q y) (q x) ≤ infDist (q x) B)
    (hpreserve : ∀x ∈ Ω, ∀a b : ℝ,
      (∀j, weight j x ≠ 0 → ∀y ∈ W j, u (q y) ∈ Icc a b) → w x ∈ Icc a b)
    (hu : ∀x, u x ∈ Icc 0 1) {s : X} (hs : s ∈ B) (hUs : s ∈ closure U) :
    liminf u (𝓝[U] s) ≤ liminf v (𝓝[U] s) ∧
      limsup v (𝓝[U] s) ≤ limsup u (𝓝[U] s) := by
  apply band_inclusion_of_eventual_interval_preservation U u v hUs hu
  intro a b hab
  exact quotient_sampling_eventual_bounds Ω U B q weight W u v w
    hq hcover hvalue hW hclose hpreserve hs hab

end CircleDomainRigidity

end

end OAI
