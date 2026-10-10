import OAI.Analysis.CircleDomains.Sobolev.ShrinkingRectangleCover
import OAI.Analysis.CircleDomains.Sobolev.LocalSmoothPartition

namespace OAI

/-! A countable compact smooth partition subordinate to coordinate
rectangles with the distance-to-dust sampling control. -/

open Set Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_shrinking_rectangle_partition
    {X : Type*} [MetricSpace X] (Ω : TopologicalSpace.Opens EuclideanPlane)
    (q : EuclideanPlane → X) (hq : ContinuousOn q Ω)
    (B : Set X) (hB : IsClosed B) (hne : B.Nonempty) (hqB : ∀x ∈ Ω, q x ∉ B) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : OpenPlanePartition Ω ι)
      (a b c d : ι → ℝ),
      (∀j, a j < b j ∧ c j < d j) ∧
      (∀j, euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) ⊆ Ω) ∧
      (∀j, tsupport (ρ.weight j) ⊆
        euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (d j))) ∧
      (∀j x, x ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) →
        ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)),
          dist (q y) (q x) ≤ Metric.infDist (q x) B) := by
  choose a b c d hab hcd hpoint hrect hpair using
    fun x : Ω => exists_small_closed_coordinate_rectangle Ω.isOpen q hq B hB hne
      x.property (hqB x x.property)
  let U : Ω → Set Ω := fun x => (fun y : Ω => euclideanPlaneCoordinates y) ⁻¹'
    (Ioo (a x) (b x) ×ˢ Ioo (c x) (d x))
  have hU (x : Ω) : U x ∈ 𝓝 x := by
    apply IsOpen.mem_nhds
    · exact (isOpen_Ioo.prod isOpen_Ioo).preimage
        (euclideanPlaneCoordinates.continuous.comp continuous_subtype_val)
    · exact hpoint x
  obtain ⟨ι, hι, ρ, center, hsub⟩ := exists_openPlanePartition Ω U hU
  refine ⟨ι, hι, ρ, a ∘ center, b ∘ center, c ∘ center, d ∘ center,
    fun j => ⟨hab (center j), hcd (center j)⟩, fun j => hrect (center j), ?_, ?_⟩
  · intro j x hx
    obtain ⟨y, hy, rfl⟩ := hsub j hx
    exact hy
  · intro j x hx y hy
    exact hpair (center j) y hy x hx

end CircleDomainRigidity

end

end OAI
