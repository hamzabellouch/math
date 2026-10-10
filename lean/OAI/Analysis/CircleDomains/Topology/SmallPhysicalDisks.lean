import OAI.Analysis.CircleDomains.Sobolev.SmoothJordanNeighborhoods
import OAI.Analysis.CircleDomains.Topology.ComponentLocalization
import OAI.Analysis.CircleDomains.Topology.QuotientTopology

namespace OAI

/-!
# Small physical disks at singleton quotient components

A singleton component of a closed quotient obstacle has a compact relatively
clopen neighborhood inside any prescribed open neighborhood. Pulling it back
and applying the proved smooth contour construction gives actual physical
Jordan disks. The boundaries avoid the entire quotient obstacle, and hence
lie in the physical domain whenever that obstacle contains the collapsed
complementary components.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- The compact relatively clopen obstacle piece used before smoothing. -/
theorem exists_compact_piece_of_singleton_component
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ A : Set X, IsCompact A ∧ x ∈ A ∧ A ⊆ F ∧ A ⊆ V ∧ IsClosed (F \ A) := by
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let xf : F := ⟨x, hx⟩
  have hcomp : connectedComponent xf = {xf} := by
    apply Set.Subset.antisymm
    · intro y hy
      have hy' : y.val ∈ connectedComponentIn F x := by
        rw [connectedComponentIn_eq_image hx]
        exact ⟨y, hy, rfl⟩
      rw [hcomponent] at hy'
      exact mem_singleton_iff.mpr (Subtype.ext (mem_singleton_iff.mp hy'))
    · exact singleton_subset_iff.mpr mem_connectedComponent
  obtain ⟨B, hB, hxB, hBV⟩ := exists_clopen_neighborhood_of_singleton_component xf hcomp
    (hV.preimage continuous_subtype_val) hxV
  let A : Set X := Subtype.val '' B
  have hdiff : F \ A = Subtype.val '' Bᶜ := by
    ext y
    constructor
    · rintro ⟨hyF, hyA⟩
      exact ⟨⟨y, hyF⟩, fun h => hyA ⟨⟨y, hyF⟩, h, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := Subtype.ext hzy
      exact hy (hzy' ▸ hz)
  refine ⟨A, hB.isClosed.isCompact.image continuous_subtype_val,
    ⟨xf, hxB, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.property
  · rintro _ ⟨y, hy, rfl⟩
    exact hBV hy
  · rw [hdiff]
    exact hF.isClosedMap_subtype_val _ hB.isOpen.isClosed_compl

/-- Closed sphere sets avoiding infinity have compact finite-coordinate
preimages. This is the concrete properness needed for the obstacle piece. -/
theorem isCompact_finite_preimage {K : Set Sphere} (hK : IsClosed K) (hinfty : OnePoint.infty ∉ K) :
    IsCompact (((↑) : ℂ → Sphere) ⁻¹' K) :=
  ((OnePoint.isClosed_iff_of_notMem hinfty).mp hK).2

/-- Finite smooth disk cover of the physical fiber at a singleton quotient
component. The connected unbounded complement condition is imposed on the
specified physical preimage, exactly where the filling argument uses it. -/
theorem exists_small_physical_disks_at_singleton_component
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (π : Sphere → X) (hπ : Continuous π) {F V : Set X}
    (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hinfty : π OnePoint.infty ∉ V)
    (hVconn : IsPreconnected ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ)
    (hVunbounded : ¬ Bornology.IsBounded ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ)
    {G : Set Sphere} (hbad : ∀ p ∈ Gᶜ, π p ∈ F) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      s.Finite ∧
      (∀ z : ℂ, π (z : Sphere) = x → z ∈ ⋃ i ∈ s, jordanInterior (H i)) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧ frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F) := by
  obtain ⟨A, hAc, hxA, hAF, hAV, hFA⟩ :=
    exists_compact_piece_of_singleton_component hF hx hcomponent hV hxV
  let q : ℂ → X := fun z => π (z : Sphere)
  have hq : Continuous q := hπ.comp OnePoint.continuous_coe
  have hAp : IsCompact (q ⁻¹' A) := by
    apply isCompact_finite_preimage (hAc.isClosed.preimage hπ)
    exact fun h => hinfty (hAV h)
  have hFp : IsClosed ((q ⁻¹' F) \ (q ⁻¹' A)) := by
    simpa only [preimage_sdiff] using hFA.preimage hq
  obtain ⟨f, t, γ, H, s, hs, hcov, hd, hinside, hcurves⟩ :=
    exists_finite_smooth_jordan_cover hsard hschoenflies hAp
      (preimage_mono hAF) hFp (hV.preimage hq) (preimage_mono hAV) hVconn hVunbounded
  refine ⟨f, t, γ, H, s, hs, ?_, hd, hinside, ?_⟩
  · intro z hz
    apply hcov
    change π (z : Sphere) ∈ A
    simpa only [hz] using hxA
  · intro i hi
    obtain ⟨hγsmooth, hγemb, hγfront, havoid⟩ := hcurves i hi
    refine ⟨hγsmooth, hγemb, hγfront, ?_⟩
    intro z hz
    have hnotF : π (z : Sphere) ∉ F := fun h => Set.disjoint_left.mp havoid hz h
    refine ⟨?_, hnotF⟩
    by_contra h
    exact hnotF (hbad _ h)

end CircleDomainRigidity

end OAI
