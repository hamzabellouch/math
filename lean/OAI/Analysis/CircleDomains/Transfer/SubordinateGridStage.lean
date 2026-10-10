import OAI.Analysis.CircleDomains.Transfer.GridStageContours
import OAI.Analysis.CircleDomains.Selection.SubordinateDustCover

namespace OAI

/-! One descending grid stage retains a prescribed local branch
neighborhood for every selected closed filling disk. -/

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_subordinate_grid_stage_contours
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B A W J F : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hA : IsCompact A) (hAB : A ⊆ B) (hBA : IsClosed (B \ A))
    (hW : IsOpen W) (hAW : A ⊆ W) (hinfty : π OnePoint.infty ∉ A)
    (hJ : IsClosed J) (hF : IsClosed F) (hBF : B ⊆ F)
    (hsingle : ∀ x ∈ A ∩ J, connectedComponentIn F x = {x})
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B)
    (Nbh : A → Set Sphere) (hNbh : ∀ a, IsOpen (Nbh a))
    (haNbh : ∀ a, a.val ∈ Nbh a) :
    ∃ (n : ℕ) (H : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ),
      ((fun z : ℂ => π (z : Sphere)) ⁻¹' (A ∩ J) ⊆ ⋃ i, jordanInterior (H i)) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      ∀ i, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' W ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F) ∧
        ∃ a : A, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' Nbh a := by
  classical
  obtain ⟨m, D, _, hcover, hdisj, hD⟩ :=
    exists_subordinate_smooth_physical_dust_cover hsard hschoenflies G π hπ
      hclosed hsurj hr hB hTD hA hAB hBA hW hAW hinfty hbad Nbh hNbh haNbh
  let q : ℂ → Sphere := fun z => π (z : Sphere)
  let V : Fin m → Set Sphere := fun i => π '' (((↑) : ℂ → Sphere) '' jordanInterior (D i))
  let Q : Fin m → Set Sphere := fun i =>
    π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior (D i)))
  let T : Fin m → Set Sphere := fun i => (A ∩ J) ∩ Q i
  have hboundary (i : Fin m) (z : ℂ) (hz : z ∈ frontier (jordanInterior (D i))) :
      (z : Sphere) ∈ G := ((hD i).2.2.2.2.1 z hz).1
  have hVo (i : Fin m) : IsOpen (V i) :=
    isOpen_image_jordanInterior_of_component_collapse G π hπ hclosed hsurj hr
      (D i) (hboundary i)
  have hqV (i : Fin m) : q ⁻¹' V i = jordanInterior (D i) :=
    physical_preimage_image_jordanInterior G π hsurj hr (D i) (hboundary i)
  have hTc (i : Fin m) : IsCompact (T i) :=
    (hA.inter_right hJ).inter_right
      ((((isCompact_closure_jordanInterior (D i)).image OnePoint.continuous_coe).image hπ).isClosed)
  have hTV (i : Fin m) : T i ⊆ V i := by
    rintro x ⟨hx, z, hz, hzx⟩
    obtain ⟨w, hw, rfl⟩ := hz
    by_cases hwU : w ∈ jordanInterior (D i)
    · exact ⟨(w : Sphere), ⟨w, hwU, rfl⟩, hzx⟩
    · have hwfront : w ∈ frontier (jordanInterior (D i)) := by
        rw [(jordanInterior_isOpen (D i)).frontier_eq]
        exact ⟨hw, hwU⟩
      exact (((hD i).2.2.2.2.1 w hwfront).2 (hzx.symm ▸ hAB hx.1)).elim
  have hVphys (i : Fin m) : IsPreconnected (q ⁻¹' V i)ᶜ ∧
      ¬ Bornology.IsBounded (q ⁻¹' V i)ᶜ :=
    physical_exterior_connected_unbounded_of_component_collapse G π hπ hclosed hsurj hr
      (hVo i)
      (isConnected_compl_image_jordanInterior_of_component_collapse
        G π hπ hsurj hr (D i) (hboundary i))
      (infty_notMem_closure_image_jordanInterior G π hπ hclosed hsurj hr
        (D i) (hboundary i))
  have hlocal (i : Fin m) := exists_physical_contours_for_compact_singleton_target
    hsard hschoenflies π hπ hF (hTc i)
      (fun _ hx => hBF (hAB hx.1.1))
      (fun x hx => hsingle x hx.1) (hVo i) (hTV i)
      (fun h => infty_notMem_closure_image_jordanInterior G π hπ hclosed hsurj hr
        (D i) (hboundary i) (subset_closure h))
      (hVphys i).1 (hVphys i).2 (fun p hp => hBF (hbad p hp))
  choose f t γ H s hs hc hd hi hcurves using hlocal
  let : ∀ i : Fin m, Fintype (s i) := fun i => (hs i).fintype
  let P := Σ i : Fin m, s i
  let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  let K : P → ℂ ≃ₜ ℂ := fun p => H p.1 p.2
  have hKinside (p : P) : closure (jordanInterior (K p)) ⊆ jordanInterior (D p.1) := by
    rw [← hqV p.1]
    exact hi p.1 p.2 p.2.property
  have hKdisj : Pairwise (Disjoint on fun p => closure (jordanInterior (K p))) := by
    intro p r hpr
    by_cases heq : p.1 = r.1
    · obtain ⟨i, p⟩ := p
      obtain ⟨j, r⟩ := r
      dsimp at heq
      subst j
      apply hd i p.property r.property
      intro h
      apply hpr
      exact congrArg (Sigma.mk i) (Subtype.ext h)
    · exact (hdisj heq).mono ((hKinside p).trans subset_closure)
        ((hKinside r).trans subset_closure)
  refine ⟨Fintype.card P, (fun k => K (e.symm k)),
    (fun k => γ (e.symm k).1 (e.symm k).2), ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hzi⟩ := mem_iUnion.mp (hcover hz.1)
    have hzT : q z ∈ T i :=
      ⟨hz, (mem_image_of_mem π (mem_image_of_mem ((↑) : ℂ → Sphere) (subset_closure hzi)))⟩
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp (hc i hzT)
    refine mem_iUnion.mpr ⟨e ⟨i, ⟨j, hj⟩⟩, ?_⟩
    simpa only [e.symm_apply_apply] using hzj
  · intro i j hij
    exact hKdisj (fun h => hij (e.symm.injective h))
  · intro i
    let p := e.symm i
    obtain ⟨hsm, hemb, hfront, hav⟩ := hcurves p.1 p.2 p.2.property
    obtain ⟨a, ha⟩ := (hD p.1).2.2.2.2.2
    exact ⟨(hKinside p).trans (subset_closure.trans (hD p.1).1),
      hsm, hemb, hfront, hav, a, (hKinside p).trans (subset_closure.trans ha)⟩

end CircleDomainRigidity

end OAI
