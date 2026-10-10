import OAI.Analysis.CircleDomains.Topology.SmallPhysicalDisks

namespace OAI

/-!
# Isolating a compact family of singleton components

A compact target consisting of singleton obstacle components has one compact
relatively clopen obstacle neighborhood inside any prescribed open set.
This strengthens pointwise isolation to the compact targets used at each
stage of the descending grid construction.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_compact_piece_cover_of_singleton_components
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F T V : Set X} (hF : IsClosed F) (hT : IsCompact T) (hTF : T ⊆ F)
    (hcomponents : ∀ x ∈ T, connectedComponentIn F x = {x})
    (hV : IsOpen V) (hTV : T ⊆ V) :
    ∃ A : Set X, IsCompact A ∧ T ⊆ A ∧ A ⊆ F ∧ A ⊆ V ∧ IsClosed (F \ A) := by
  classical
  choose C hCc hxC hCF hCV hFC using fun x : T =>
    exists_compact_piece_of_singleton_component hF (hTF x.property)
      (hcomponents x x.property) hV (hTV x.property)
  obtain ⟨s, hs⟩ := hT.elim_finite_subcover (fun x : T => (F \ C x)ᶜ)
    (fun x => (hFC x).isOpen_compl) (by
      intro x hx
      refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
      exact fun h => h.2 (hxC ⟨x, hx⟩))
  let A := ⋃ x ∈ s, C x
  have hdiff : F \ A = F ∩ ⋂ x ∈ s, (F \ C x) := by
    ext z
    simp only [A, mem_sdiff, mem_iUnion, mem_inter_iff, mem_iInter, not_exists]
    constructor
    · rintro ⟨hzF, hzC⟩
      exact ⟨hzF, fun x hx => ⟨hzF, hzC x hx⟩⟩
    · rintro ⟨hzF, hzC⟩
      exact ⟨hzF, fun x hx => (hzC x hx).2⟩
  refine ⟨A, s.isCompact_biUnion (fun x _ => hCc x), ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    have hxyC : x ∈ C y := by
      by_contra h
      exact hxy ⟨hTF hx, h⟩
    exact mem_iUnion₂.mpr ⟨y, hy, hxyC⟩
  · exact iUnion₂_subset fun x _ => hCF x
  · exact iUnion₂_subset fun x _ => hCV x
  · rw [hdiff]
    exact hF.inter (isClosed_biInter (fun x _ => hFC x))

/-- Compact-target version of the physical contour construction. This is
used inside one preliminary disk at a fixed label stage. -/
theorem exists_physical_contours_for_compact_singleton_target
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (π : Sphere → X) (hπ : Continuous π) {F T V : Set X}
    (hF : IsClosed F) (hT : IsCompact T) (hTF : T ⊆ F)
    (hcomponents : ∀ x ∈ T, connectedComponentIn F x = {x})
    (hV : IsOpen V) (hTV : T ⊆ V) (hinfty : π OnePoint.infty ∉ V)
    (hVconn : IsPreconnected ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ)
    (hVunbounded : ¬ Bornology.IsBounded ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ)
    {G : Set Sphere} (hbad : ∀ p ∈ Gᶜ, π p ∈ F) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      s.Finite ∧ ((fun z : ℂ => π (z : Sphere)) ⁻¹' T ⊆ ⋃ i ∈ s, jordanInterior (H i)) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧ frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F) := by
  obtain ⟨A, hAc, hTA, hAF, hAV, hFA⟩ :=
    exists_compact_piece_cover_of_singleton_components hF hT hTF hcomponents hV hTV
  let q : ℂ → X := fun z => π (z : Sphere)
  have hq : Continuous q := hπ.comp OnePoint.continuous_coe
  have hAp : IsCompact (q ⁻¹' A) :=
    isCompact_finite_preimage (hAc.isClosed.preimage hπ) (fun h => hinfty (hAV h))
  have hFp : IsClosed ((q ⁻¹' F) \ (q ⁻¹' A)) := by
    simpa only [preimage_sdiff] using hFA.preimage hq
  obtain ⟨f, t, γ, H, s, hs, hcov, hd, hinside, hcurves⟩ :=
    exists_finite_smooth_jordan_cover hsard hschoenflies hAp
      (preimage_mono hAF) hFp (hV.preimage hq) (preimage_mono hAV) hVconn hVunbounded
  refine ⟨f, t, γ, H, s, hs, (preimage_mono hTA).trans hcov, hd, hinside, ?_⟩
  intro i hi
  obtain ⟨hsmooth, hemb, hfront, havoid⟩ := hcurves i hi
  refine ⟨hsmooth, hemb, hfront, ?_⟩
  intro z hz
  have hnotF : π (z : Sphere) ∉ F := fun h => Set.disjoint_left.mp havoid hz h
  refine ⟨?_, hnotF⟩
  by_contra h
  exact hnotF (hbad _ h)

end CircleDomainRigidity

end OAI
