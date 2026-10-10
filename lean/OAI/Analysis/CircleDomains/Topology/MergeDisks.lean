import OAI.Analysis.CircleDomains.Topology.SmallQuotientDisks

namespace OAI

/-!
# Merging finite physical disk families away from an obstacle

Section 2, Step 3 of the Koebe manuscript merges overlapping preliminary
disks without introducing intersections of new boundaries with the lower
grid obstacle. A regular cutoff gives the same merge directly: if `Q` is
their compact union and its boundary misses `F`, then `Q` is relatively
clopen in `F ∪ Q`. The established contour construction applied to that
larger obstacle covers all of `Q` by disjoint smooth Jordan disks.
No transversality or general-position input is required.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- A compact region whose frontier misses a closed obstacle is relatively
clopen after it is adjoined to that obstacle. -/
theorem isClosed_diff_of_frontier_disjoint
    {Q F : Set ℂ} (hQ : IsClosed Q) (hF : IsClosed F)
    (hboundary : Disjoint (frontier Q) F) : IsClosed (F \ Q) := by
  have heq : F \ Q = F \ interior Q := by
    apply Set.Subset.antisymm
    · exact sdiff_subset_sdiff_right interior_subset
    · rintro z ⟨hzF, hzint⟩
      refine ⟨hzF, ?_⟩
      intro hzQ
      apply Set.disjoint_left.mp hboundary _ hzF
      rw [frontier, hQ.closure_eq]
      exact ⟨hzQ, hzint⟩
  rw [heq]
  exact hF.sdiff isOpen_interior

/-- Smooth and fill a compact region while keeping every new boundary
away from a closed obstacle. Disjointness is for the full closed fills. -/
theorem exists_smooth_jordan_cover_of_frontier_avoidance
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {Q F V : Set ℂ} (hQ : IsCompact Q) (hF : IsClosed F)
    (hboundary : Disjoint (frontier Q) F)
    (hV : IsOpen V) (hQV : Q ⊆ V) (hVconn : IsPreconnected Vᶜ)
    (hVunbounded : ¬ Bornology.IsBounded Vᶜ) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      s.Finite ∧ (Q ⊆ ⋃ i ∈ s, jordanInterior (H i)) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆ V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧ frontier (jordanInterior (H i)) = range (γ i) ∧
        Disjoint (frontier (jordanInterior (H i))) F := by
  have hdiff : IsClosed ((F ∪ Q) \ Q) := by
    simpa only [union_sdiff_right] using
      isClosed_diff_of_frontier_disjoint hQ.isClosed hF hboundary
  obtain ⟨f, t, γ, H, s, hs, hcover, hpair, hinside, hcurves⟩ :=
    exists_finite_smooth_jordan_cover hsard hschoenflies hQ
      subset_union_right hdiff hV hQV hVconn hVunbounded
  refine ⟨f, t, γ, H, s, hs, hcover, hpair, hinside, ?_⟩
  intro i hi
  obtain ⟨hsmooth, hemb, hfront, havoid⟩ := hcurves i hi
  exact ⟨hsmooth, hemb, hfront, havoid.mono_right subset_union_left⟩

/-- Merge any finite family of closed Jordan disks, including overlapping
ones, into disjoint smooth closed fills in the same container. It suffices
that the original boundary curves miss the obstacle. -/
theorem exists_merged_smooth_jordan_disks
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} [Finite I] (D : I → ℂ ≃ₜ ℂ)
    {F V : Set ℂ} (hF : IsClosed F)
    (havoid : ∀ i, Disjoint (frontier (jordanInterior (D i))) F)
    (hV : IsOpen V) (hDV : ∀ i, closure (jordanInterior (D i)) ⊆ V)
    (hVconn : IsPreconnected Vᶜ) (hVunbounded : ¬ Bornology.IsBounded Vᶜ) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      s.Finite ∧ (⋃ i, closure (jordanInterior (D i))) ⊆ (⋃ i ∈ s, jordanInterior (H i)) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆ V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧ frontier (jordanInterior (H i)) = range (γ i) ∧
        Disjoint (frontier (jordanInterior (H i))) F := by
  have hfront (i : I) : frontier (closure (jordanInterior (D i))) =
      frontier (jordanInterior (D i)) := by
    rw [frontier, closure_closure, interior_closure_jordanInterior,
      ← (jordanInterior_isOpen (D i)).frontier_eq]
  have hfrontQ : frontier (⋃ i, closure (jordanInterior (D i))) ⊆
      ⋃ i, frontier (jordanInterior (D i)) := by
    simpa only [mem_univ, iUnion_true, hfront] using
      (Set.toFinite (univ : Set I)).frontier_biUnion_subset
        (fun i => closure (jordanInterior (D i)))
  apply exists_smooth_jordan_cover_of_frontier_avoidance hsard hschoenflies
    (isCompact_iUnion (fun i => isCompact_closure_jordanInterior (D i))) hF
    _ hV (iUnion_subset hDV) hVconn hVunbounded
  apply Set.disjoint_left.mpr
  intro z hz hzF
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hfrontQ hz)
  exact Set.disjoint_left.mp (havoid i) hi hzF

end CircleDomainRigidity

end OAI
