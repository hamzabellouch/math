import OAI.Analysis.CircleDomains.Sobolev.SmallShrinkingRectanglePartition

namespace OAI

/-! The shrinking rectangle construction can respect specified open sampling neighborhoods. -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem exists_small_shrinking_partition_refining_neighborhoods
    {X : Type*} [MetricSpace X] (Ω : TopologicalSpace.Opens EuclideanPlane)
    (q : EuclideanPlane → X) (hq : ContinuousOn q Ω)
    (B : Set X) (hB : IsClosed B) (hne : B.Nonempty) (hqB : ∀x ∈ Ω, q x ∉ B)
    (N : Ω → Set EuclideanPlane) (hN : ∀x, IsOpen (N x)) (hxN : ∀x : Ω, x.val ∈ N x) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : OpenPlanePartition Ω ι) (center : ι → Ω)
      (a b c d : ι → ℝ),
      (∀j, a j < b j ∧ c j < d j) ∧
      (∀j, euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) ⊆ Ω ∩ N (center j)) ∧
      (∀j, tsupport (ρ.weight j) ⊆
        euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (d j))) ∧
      (∀j x, x ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) →
        ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)),
          dist (q y) (q x) ≤ Metric.infDist (q x) B) ∧
      (∀j x, x ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) →
        ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)),
          dist (⟨x 0, x 1⟩ : ℂ) (⟨y 0, y 1⟩ : ℂ) ≤ 1) := by
  choose a b c d hab hcd hpoint hrect hpair hdiam using
    fun x : Ω => exists_small_closed_coordinate_rectangle_with_diameter
      (Ω.isOpen.inter (hN x)) q (hq.mono inter_subset_left) B hB hne
      (show x.val ∈ (Ω : Set EuclideanPlane) ∩ N x from ⟨x.property, hxN x⟩)
      (hqB x x.property)
  let U : Ω → Set Ω := fun x => (fun y : Ω => euclideanPlaneCoordinates y) ⁻¹'
    (Ioo (a x) (b x) ×ˢ Ioo (c x) (d x))
  have hU (x : Ω) : U x ∈ 𝓝 x := by
    apply IsOpen.mem_nhds
    · exact (isOpen_Ioo.prod isOpen_Ioo).preimage
        (euclideanPlaneCoordinates.continuous.comp continuous_subtype_val)
    · exact hpoint x
  obtain ⟨ι, hι, ρ, center, hsub⟩ := exists_openPlanePartition Ω U hU
  refine ⟨ι, hι, ρ, center, a ∘ center, b ∘ center, c ∘ center, d ∘ center,
    fun j => ⟨hab (center j), hcd (center j)⟩, fun j => hrect (center j), ?_, ?_, ?_⟩
  · intro j x hx
    obtain ⟨y, hy, rfl⟩ := hsub j hx
    exact hy
  · intro j x hx y hy
    exact hpair (center j) y hy x hx

  · intro j x hx y hy
    exact hdiam (center j) x hx y hy

end CircleDomainRigidity

end

end OAI
