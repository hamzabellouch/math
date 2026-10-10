import OAI.Analysis.CircleDomains.Modulus.WeightedJordanCovers
import OAI.Analysis.CircleDomains.Topology.SinglePhysicalDisk

namespace OAI

/-! A finite-cost smooth collar around a connected compact set, avoiding
an outer closed obstacle. Used to place joining levels between fixed gates. -/

open Set Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

private theorem isClosed_diff_of_frontier_disjoint {X : Type*} [TopologicalSpace X]
    {A F : Set X} (hA : IsClosed A) (hF : IsClosed F) (hFA : Disjoint F (frontier A)) :
    IsClosed (F \ A) := by
  have heq : F \ A = F \ interior A := by
    ext x
    constructor
    · intro h
      exact ⟨h.1, fun hx => h.2 (interior_subset hx)⟩
    · rintro ⟨hxF, hxI⟩
      refine ⟨hxF, ?_⟩
      intro hxA
      exact Set.disjoint_left.mp hFA hxF ⟨hA.closure_eq.symm ▸ hxA, hxI⟩
  rw [heq]
  exact hF.inter isOpen_interior.isClosed_compl

theorem exists_weighted_collar_around_compact
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    {A F V : Set ℂ} (hA : IsCompact A) (hconn : IsConnected A)
    (hF : IsClosed F) (hFA : Disjoint F (frontier A))
    (hV : IsOpen V) (hAV : A ⊆ V)
    (hVc : IsPreconnected Vᶜ) (hVun : ¬ Bornology.IsBounded Vᶜ)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ) (f : ℂ → ℝ) (t : ℝ),
      A ⊆ jordanInterior H ∧ closure (jordanInterior H) ⊆ V ∧
      ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) (↑(⊤ : ℕ∞)) γ ∧ Topology.IsEmbedding γ ∧
      frontier (jordanInterior H) = range γ ∧
      frontier (jordanInterior H) ⊆ {z | f z = t} ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ IsPlanarRegularValue f t ∧
      {z | f z = t} ⊆ V \ (A ∪ F) ∧
      (∫⁻z in {z | f z = t}, g z ∂(μH[1] : Measure ℂ)) < ∞ := by
  have hdiff : IsClosed ((A ∪ F) \ A) := by
    simpa only [union_sdiff_distrib, sdiff_self, empty_union] using
      isClosed_diff_of_frontier_disjoint hA.isClosed hF hFA
  obtain ⟨f, t, γ, H, s, hf, hreg, hlevel, havoid, hcost, _, hcover, hpair,
    hinside, hcurves⟩ := exists_finite_weighted_jordan_cover hcoarea hsard hsch
      hA subset_union_left hdiff hV hAV hVc hVun g hg hg2
  have hpair' : Pairwise (Disjoint on fun i : s => jordanInterior (H i)) := by
    intro i j hij
    exact (hpair i.property j.property (fun h => hij (Subtype.ext h))).mono
      subset_closure subset_closure
  have hcover' : A ⊆ ⋃i : s, jordanInterior (H i) := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcover hz)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  obtain ⟨i, hi⟩ := exists_member_containing_connected_set hconn
    (fun i : s => jordanInterior (H i)) (fun i => jordanInterior_isOpen (H i)) hpair' hcover'
  obtain ⟨hγ, hemb, hfront, _, hfrontlevel⟩ := hcurves i i.property
  refine ⟨H i, γ i, f, t, hi, hinside i i.property, hγ, hemb, hfront,
    hfrontlevel, hf, hreg, ?_, hcost⟩
  intro z hz
  exact ⟨hlevel hz, fun h => Set.disjoint_left.mp havoid hz h⟩

end CircleDomainRigidity

end

end OAI
