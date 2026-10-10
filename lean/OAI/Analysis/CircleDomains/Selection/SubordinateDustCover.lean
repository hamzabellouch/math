import OAI.Analysis.CircleDomains.Selection.FiniteDustCover

namespace OAI

/-! Preliminary smooth dust covers subordinate to prescribed local
branch neighborhoods. This retains which neighborhood contains each
closed physical fill, for the mixed period-coordinate construction. -/

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_subordinate_smooth_physical_dust_cover
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B A W : Set Sphere} (_hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hA : IsCompact A) (hAB : A ⊆ B) (hBA : IsClosed (B \ A))
    (hW : IsOpen W) (hAW : A ⊆ W) (hinfty : π OnePoint.infty ∉ A)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B)
    (Q : A → Set Sphere) (hQ : ∀ a, IsOpen (Q a)) (haQ : ∀ a, a.val ∈ Q a) :
    ∃ (n : ℕ) (H : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ),
      ((fun z : ℂ => π (z : Sphere)) ⁻¹' A ⊆ ⋃ i, jordanInterior (H i)) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      ∀ i, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' W ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) ∧
        ∃ a : A, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' Q a := by
  classical
  have hlocal (a : A) : ∃ V : Set Sphere, IsOpen V ∧ a.val ∈ V ∧
      closure V ⊆ (W ∩ {π OnePoint.infty}ᶜ) ∩ Q a ∧ IsConnected Vᶜ := by
    apply exists_sphere_neighborhood_connected_compl
      ((hW.inter isClosed_singleton.isOpen_compl).inter (hQ a))
    exact ⟨⟨hAW a.property, fun heq => hinfty (heq ▸ a.property)⟩, haQ a⟩
  choose V hVo haV hVW hVc using hlocal
  obtain ⟨m, C, a, hC, hCd, hCcover⟩ := exists_compact_clopen_refinement hA
    (fun T hT hconn => hTD T (hT.trans hAB) hconn) V hVo haV
  let q : ℂ → Sphere := fun z => π (z : Sphere)
  have hq : Continuous q := hπ.comp OnePoint.continuous_coe
  have hCpi (i : Fin m) : π OnePoint.infty ∉ C i := by
    intro h
    exact (hVW (a i) (subset_closure ((hC i).2.2.1 h))).1.2 rfl
  have hCp (i : Fin m) : IsCompact (q ⁻¹' C i) :=
    isCompact_finite_preimage ((hC i).1.isClosed.preimage hπ) (hCpi i)
  have hCpd : Pairwise (Disjoint on fun i => q ⁻¹' C i) := by
    intro i j hij
    exact (hCd hij).preimage q
  have hCsub (i : Fin m) : q ⁻¹' C i ⊆ q ⁻¹' B :=
    preimage_mono ((hC i).2.1.trans hAB)
  have hdiff (i : Fin m) : IsClosed ((q ⁻¹' B) \ (q ⁻¹' C i)) := by
    have heq : B \ C i = (B \ A) ∪ (A \ C i) := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzB, hzC⟩
        by_cases hzA : z ∈ A
        · exact Or.inr ⟨hzA, hzC⟩
        · exact Or.inl ⟨hzB, hzA⟩
      · rintro z (hz | hz)
        · exact ⟨hz.1, fun hzC => hz.2 ((hC i).2.1 hzC)⟩
        · exact ⟨hAB hz.1, hz.2⟩
    have hc : IsClosed (B \ C i) := by
      rw [heq]
      exact hBA.union (hC i).2.2.2
    simpa only [preimage_sdiff] using hc.preimage hq
  have hVpu (i : Fin m) : IsPreconnected (q ⁻¹' V (a i))ᶜ ∧
      ¬ Bornology.IsBounded (q ⁻¹' V (a i))ᶜ := by
    apply physical_exterior_connected_unbounded_of_component_collapse
      G π hπ hclosed hsurj hr (hVo (a i)) (hVc (a i))
    exact fun h => (hVW (a i) h).1.2 rfl
  obtain ⟨f, t, γ, H, s, hs, hcover, hpair, hcurves⟩ :=
    exists_disjoint_dust_contours hsard hschoenflies (fun i => q ⁻¹' C i)
      (fun i => q ⁻¹' V (a i)) (q ⁻¹' B) hCp hCpd hCsub hdiff
      (fun i => (hVo (a i)).preimage hq) (fun i => preimage_mono (hC i).2.2.1)
      (fun i => (hVpu i).1) (fun i => (hVpu i).2)
  let : Fintype s := hs.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  refine ⟨Fintype.card s, (fun i => H (e.symm i)), (fun i => γ (e.symm i)), ?_, ?_, ?_⟩
  · intro z hz
    have hzC : q z ∈ ⋃ i, C i := hCcover.symm ▸ hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzC
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp (hcover (mem_iUnion.mpr ⟨i, hi⟩))
    refine mem_iUnion.mpr ⟨e ⟨p, hp⟩, ?_⟩
    simpa only [e.symm_apply_apply] using hzp
  · intro i j hij
    exact hpair (e.symm i).property (e.symm j).property
      (fun h => hij (e.symm.injective (Subtype.ext h)))
  · intro i
    let p := e.symm i
    obtain ⟨hinside, hsmooth, hemb, hfront, havoid⟩ := hcurves p p.property
    refine ⟨?_, hsmooth, hemb, hfront, ?_, a p.val.1, ?_⟩
    · exact hinside.trans (preimage_mono (subset_closure.trans
        (fun z hz => (hVW (a p.val.1) hz).1.1)))
    · intro z hz
      have hnotB : π (z : Sphere) ∉ B := fun h => Set.disjoint_left.mp havoid hz h
      refine ⟨?_, hnotB⟩
      by_contra h
      exact hnotB (hbad _ h)

    · exact hinside.trans (preimage_mono (subset_closure.trans
        (fun z hz => (hVW (a p.val.1) hz).2)))

end CircleDomainRigidity

end OAI
