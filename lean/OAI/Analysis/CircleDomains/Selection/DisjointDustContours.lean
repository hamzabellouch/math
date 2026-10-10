import OAI.Analysis.CircleDomains.Topology.SaturatedDisks
import OAI.Analysis.CircleDomains.Selection.DustCover

namespace OAI

/-!
# Simultaneous contours for finitely many clopen dust pieces

Disjoint compact physical pieces have disjoint open neighborhoods. Regular
contours and the outer subfamily of their combined family have disjoint
closed fills inside the prescribed connected-complement containers.
-/

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_disjoint_dust_contours
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} [Finite I] (A V : I → Set ℂ) (F : Set ℂ)
    (hAc : ∀ i, IsCompact (A i)) (hAd : Pairwise (Disjoint on A))
    (hAF : ∀ i, A i ⊆ F) (hFA : ∀ i, IsClosed (F \ A i))
    (hVo : ∀ i, IsOpen (V i)) (hAV : ∀ i, A i ⊆ V i)
    (hVc : ∀ i, IsPreconnected (V i)ᶜ)
    (hVu : ∀ i, ¬ Bornology.IsBounded (V i)ᶜ) :
    ∃ (f : I → ℂ → ℝ) (t : I → ℝ)
      (γ : (Σ i, ConnectedComponents {z // f i z = t i}) → Circle → ℂ)
      (H : (Σ i, ConnectedComponents {z // f i z = t i}) → ℂ ≃ₜ ℂ)
      (s : Set (Σ i, ConnectedComponents {z // f i z = t i})),
      s.Finite ∧ ((⋃ i, A i) ⊆ ⋃ p ∈ s, jordanInterior (H p)) ∧
      s.Pairwise (fun p q => Disjoint (closure (jordanInterior (H p)))
        (closure (jordanInterior (H q)))) ∧
      ∀ p ∈ s, closure (jordanInterior (H p)) ⊆ V p.1 ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ p) ∧ Topology.IsEmbedding (γ p) ∧
        frontier (jordanInterior (H p)) = range (γ p) ∧
        Disjoint (frontier (jordanInterior (H p))) F := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hn : Pairwise (Disjoint on fun i => 𝓝ˢ (A i)) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet (hAc i).isClosed (hAc j).isClosed (hAd hij)
  obtain ⟨W, hW, hWd⟩ := hn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet (A i))
  let O : I → Set ℂ := fun i => W i ∩ V i
  have hOo (i) : IsOpen (O i) := (hW i).1.inter (hVo i)
  have hAO (i) : A i ⊆ O i := subset_inter (hW i).2 (hAV i)
  choose f t hf ht hUo hAU hUc hUO hUF hlevel hreg havoid hfrontavoid using
    fun i => exists_regular_superlevel_isolating_obstacle hsard (hAc i) (hAF i)
      (hFA i) (hOo i) (hAO i)
  have hdata (i) := compact_regular_level_circle_contours
    (hf i) (hreg i) (hlevel i)
  have : ∀ i, Finite (ConnectedComponents {z // f i z = t i}) := fun i => (hdata i).1
  choose γ₀ hγ₀ hγd hγcover using fun i => (hdata i).2
  let γ : (Σ i, ConnectedComponents {z // f i z = t i}) → Circle → ℂ :=
    fun p => γ₀ p.1 p.2
  have hfrontU (i) : frontier {z | t i < f i z} = {z | f i z = t i} :=
    frontier_superlevel_eq_regular_level (hf i).continuous (hreg i)
  have hγO (p : Σ i, ConnectedComponents {z // f i z = t i}) : range (γ p) ⊆ O p.1 := by
    intro z hz
    apply hUO p.1
    apply frontier_subset_closure
    rw [hfrontU, ← hγcover p.1]
    exact mem_iUnion.mpr ⟨p.2, hz⟩
  have hpair : Pairwise (fun p q => Disjoint (range (γ p)) (range (γ q))) := by
    intro p q hpq
    by_cases hi : p.1 = q.1
    · obtain ⟨i, c⟩ := p
      obtain ⟨j, d⟩ := q
      dsimp at hi
      subst j
      exact hγd i (fun h => hpq (Sigma.ext rfl (heq_of_eq h)))
    · exact (hWd hi).mono (fun z hz => (hγO p hz).1) (fun z hz => (hγO q hz).1)
  choose H hH using fun p => hschoenflies (γ p) (hγ₀ p.1 p.2).2.continuous
    (hγ₀ p.1 p.2).2.injective
  have hfront (p) : frontier (jordanInterior (H p)) = range (γ p) :=
    frontier_jordanInterior_eq_circle_range (H p) (γ p) (hH p)
  have hHpair : Pairwise (fun p q => Disjoint (frontier (jordanInterior (H p)))
      (frontier (jordanInterior (H q)))) := by
    intro p q hpq
    simpa only [hfront] using hpair hpq
  obtain ⟨s, hs, hsd, hdom, _⟩ := exists_outer_jordanInteriors H hHpair
  let : Finite s := hs.to_subtype
  let U : Set ℂ := ⋃ i, {z | t i < f i z}
  have hUopen : IsOpen U := isOpen_iUnion hUo
  have hUbdd : Bornology.IsBounded U :=
    (isCompact_iUnion hUc).isBounded.subset (iUnion_mono fun _ => subset_closure)
  have hselected (p : s) : frontier (jordanInterior (H p)) ⊆ frontier U := by
    intro z hz
    have hzo : z ∈ O p.val.1 := hγO p (hfront p ▸ hz)
    have hzlevel : f p.val.1 z = t p.val.1 := by
      change z ∈ {w | f p.val.1 w = t p.val.1}
      rw [← hγcover p.val.1]
      exact mem_iUnion.mpr ⟨p.val.2, hfront p ▸ hz⟩
    rw [hUopen.frontier_eq]
    refine ⟨?_, ?_⟩
    · apply closure_mono (subset_iUnion (fun i => {z | t i < f i z}) p.val.1)
      apply frontier_subset_closure
      rwa [hfrontU]
    · intro hzU
      obtain ⟨j, hzj⟩ := mem_iUnion.mp hzU
      by_cases hij : p.val.1 = j
      · subst j
        change t p.val.1 < f p.val.1 z at hzj
        linarith [hzlevel]
      · have hzjO := hUO j (subset_closure hzj)
        exact Set.disjoint_left.mp (hWd hij) hzo.1 hzjO.1
  have hcover : frontier U ⊆ ⋃ p : s, closure (jordanInterior (H p)) := by
    intro z hz
    have hfin := (Set.toFinite (univ : Set I)).frontier_biUnion_subset
      (fun i => {z | t i < f i z})
    have hfin' : frontier U ⊆ ⋃ i, frontier {z | t i < f i z} := by
      simpa only [mem_univ, iUnion_true] using hfin
    have hzi : z ∈ ⋃ i, frontier {z | t i < f i z} := by
      exact hfin' hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzi
    rw [hfrontU, ← hγcover i] at hi
    obtain ⟨c, hc⟩ := mem_iUnion.mp hi
    let p : Σ i, ConnectedComponents {z // f i z = t i} := ⟨i, c⟩
    have hp : z ∈ closure (jordanInterior (H p)) := by
      apply frontier_subset_closure
      rw [hfront p]
      exact hc
    obtain ⟨q, hq, hpq⟩ := hdom p
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, hpq hp⟩
  have hsd' : Pairwise (Disjoint on fun p : s => closure (jordanInterior (H p))) := by
    intro p q hpq
    exact hsd p.property q.property (fun h => hpq (Subtype.ext h))
  have hUcover := open_subset_finite_jordanInteriors_of_frontier_subset
    (fun p : s => H p) hsd' hUopen hUbdd hcover hselected
  refine ⟨f, t, γ, H, s, hs, ?_, hsd, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hUcover (mem_iUnion.mpr ⟨i, hAU i hi⟩))
    exact mem_iUnion₂.mpr ⟨p, p.property, hp⟩
  · intro p _
    refine ⟨closed_jordanInterior_subset_of_unbounded_connected_compl (H p)
      (hVc p.1) (hVu p.1) ?_, (hγ₀ p.1 p.2).1, (hγ₀ p.1 p.2).2, hfront p, ?_⟩
    · exact fun z hz => (hγO p (hfront p ▸ hz)).2
    · apply (havoid p.1).mono_left
      intro z hz
      rw [← hγcover p.1]
      exact mem_iUnion.mpr ⟨p.2, hfront p ▸ hz⟩

end CircleDomainRigidity

end OAI
