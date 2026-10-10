import OAI.Analysis.CircleDomains.Sobolev.ShrinkingRectanglePartition

namespace OAI

/-! Shrinking sampling rectangles with uniformly small physical diameter. -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem exists_small_closed_coordinate_rectangle_with_diameter
    {X : Type*} [MetricSpace X] {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    (q : EuclideanPlane → X) (hq : ContinuousOn q Ω)
    (B : Set X) (hB : IsClosed B) (hne : B.Nonempty)
    {x : EuclideanPlane} (hx : x ∈ Ω) (hqx : q x ∉ B) :
    ∃a b c d : ℝ, a < b ∧ c < d ∧
      euclideanPlaneCoordinates x ∈ Ioo a b ×ˢ Ioo c d ∧
      (euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) ⊆ Ω) ∧
      (∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
        ∀z ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
          dist (q y) (q z) ≤ infDist (q z) B) ∧
      (∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
        ∀z ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
          dist (⟨y 0, y 1⟩ : ℂ) (⟨z 0, z 1⟩ : ℂ) ≤ 1) := by
  let f : EuclideanPlane → ℂ := fun y => ⟨y 0, y 1⟩
  have hf : Continuous f :=
    Complex.equivRealProdCLM.symm.continuous.comp euclideanPlaneCoordinates.continuous
  let V := (Ω ∩ q ⁻¹' ball (q x) (infDist (q x) B / 4)) ∩ f ⁻¹' ball (f x) (1 / 2)
  have hδ : 0 < infDist (q x) B / 4 := div_pos
    ((hB.notMem_iff_infDist_pos hne).1 hqx) (by norm_num)
  have hV : IsOpen V := (hq.isOpen_inter_preimage hΩ isOpen_ball).inter (isOpen_ball.preimage hf)
  have hxV : x ∈ V := ⟨⟨hx, mem_ball_self hδ⟩, mem_ball_self (by norm_num)⟩
  have hVe : IsOpen (euclideanPlaneCoordinates '' V) :=
    euclideanPlaneCoordinates.toHomeomorph.isOpenMap V hV
  obtain ⟨a, b, c, d, hab, hcd, hpoint, hrect⟩ := exists_closed_rectangle_inside_open hVe
    (mem_image_of_mem euclideanPlaneCoordinates hxV)
  have hsub : euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) ⊆ V := by
    intro y hy
    obtain ⟨z, hz, heq⟩ := hrect hy
    exact euclideanPlaneCoordinates.injective heq ▸ hz
  refine ⟨a, b, c, d, hab, hcd, hpoint, (hsub.trans inter_subset_left).trans inter_subset_left, ?_, ?_⟩
  · intro y hy z hz
    exact dist_le_infDist_of_small_ball B (hsub hz).1.2 (hsub hy).1.2
  · intro y hy z hz
    have h1 : dist (f y) (f x) < 1 / 2 := (hsub hy).2
    have h2' : dist (f z) (f x) < 1 / 2 := (hsub hz).2
    have h2 : dist (f x) (f z) < 1 / 2 := by simpa only [dist_comm] using h2'
    exact (dist_triangle (f y) (f x) (f z)).trans (by linarith)


theorem exists_small_shrinking_rectangle_partition
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
          dist (q y) (q x) ≤ Metric.infDist (q x) B) ∧
      (∀j x, x ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) →
        ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)),
          dist (⟨x 0, x 1⟩ : ℂ) (⟨y 0, y 1⟩ : ℂ) ≤ 1) := by
  choose a b c d hab hcd hpoint hrect hpair hdiam using
    fun x : Ω => exists_small_closed_coordinate_rectangle_with_diameter Ω.isOpen q hq B hB hne
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
