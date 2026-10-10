import OAI.Analysis.CircleDomains.Topology.FillingDisks
import OAI.Analysis.CircleDomains.Transfer.SubordinateGridStage

namespace OAI

/-! The complete descending finite-grid construction with each filling
cap contained in one prescribed local coordinate neighborhood. -/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_subordinate_finite_filling_disks
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (J : ℕ → Set Sphere) (hJ : ∀ j, IsClosed (J j))
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B)
    (n : ℕ) {A W : Set Sphere}
    (hA : IsCompact A) (hAB : A ⊆ B) (hBA : IsClosed (B \ A))
    (hW : IsOpen W) (hAW : A ⊆ W) (hinfty : π OnePoint.infty ∉ A)
    (hsingle : ∀ j < n, ∀ x ∈ A ∩ J j,
      connectedComponentIn (B ∪ ⋃ k ∈ Finset.range j, J k) x = {x})
    (Nbh : A → Set Sphere) (hNbh : ∀ a, IsOpen (Nbh a))
    (haNbh : ∀ a, a.val ∈ Nbh a) :
    ∃ (m : ℕ) (H : Fin m → ℂ ≃ₜ ℂ) (γ : Fin m → Circle → ℂ),
      ((fun z : ℂ => π (z : Sphere)) ⁻¹' A ⊆ ⋃ i, jordanInterior (H i)) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      ∀ i, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' W ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) ∧
        (∃ k : ℕ, ∀ j < n, j ≠ k →
          Disjoint (frontier (jordanInterior (H i))) ((fun z : ℂ => π (z : Sphere)) ⁻¹' J j)) ∧
        ∃ a : A, closure (jordanInterior (H i)) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' Nbh a := by
  classical
  induction n generalizing A W with
  | zero =>
    obtain ⟨m, H, γ, hc, hd, hcurves⟩ :=
      exists_subordinate_smooth_physical_dust_cover hsard hschoenflies G π hπ
        hclosed hsurj hr hB hTD hA hAB hBA hW hAW hinfty hbad Nbh hNbh haNbh
    refine ⟨m, H, γ, hc, hd, ?_⟩
    intro i
    exact ⟨(hcurves i).1, (hcurves i).2.1, (hcurves i).2.2.1,
      (hcurves i).2.2.2.1, (hcurves i).2.2.2.2.1, ⟨0, by simp⟩,
      (hcurves i).2.2.2.2.2⟩
  | succ n ih =>
    let q : ℂ → Sphere := fun z => π (z : Sphere)
    let F : Set Sphere := B ∪ ⋃ k ∈ Finset.range n, J k
    have hF : IsClosed F := hB.union (isClosed_biUnion_finset fun k _ => hJ k)
    obtain ⟨m, H, γ, hcover, hd, hcurves⟩ :=
      exists_subordinate_grid_stage_contours hsard hschoenflies G π hπ hclosed hsurj hr
        hB hTD hA hAB hBA hW hAW hinfty (hJ n) hF subset_union_left
        (hsingle n (Nat.lt_succ_self n)) hbad Nbh hNbh haNbh
    let U : Set Sphere := ⋃ i, π '' (((↑) : ℂ → Sphere) '' jordanInterior (H i))
    let C : Set Sphere := ⋃ i, π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior (H i)))
    let A' := A \ U
    let W' := W \ (C ∪ J n)
    have hb (i : Fin m) (z : ℂ) (hz : z ∈ frontier (jordanInterior (H i))) :
        (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B :=
      ⟨((hcurves i).2.2.2.2.1 z hz).1,
        fun h => ((hcurves i).2.2.2.2.1 z hz).2 (Or.inl h)⟩
    obtain ⟨hA'c, hA'B, hBA', hA'C⟩ :=
      compact_clopen_dust_remainder G π hπ hclosed hsurj hr H hB hA hAB hBA hb
    have hcovered : A ∩ J n ⊆ U :=
      quotient_cover_of_physical_cover π hsurj (fun i => jordanInterior (H i))
        (fun h => hinfty h.1) hcover
    have hA'Jn : Disjoint A' (J n) := remainder_avoids_covered_set hcovered
    have hC : IsClosed C := isClosed_iUnion_of_finite fun i =>
      (((isCompact_closure_jordanInterior (H i)).image OnePoint.continuous_coe).image hπ).isClosed
    have hW' : IsOpen W' := hW.sdiff (hC.union (hJ n))
    have hA'W' : A' ⊆ W' := by
      intro x hx
      refine ⟨hAW hx.1, ?_⟩
      rintro (hxC | hxJ)
      · exact Set.disjoint_left.mp hA'C hx hxC
      · exact Set.disjoint_left.mp hA'Jn hx hxJ
    obtain ⟨r, K, δ, hcK, hdK, hK⟩ := ih hA'c hA'B hBA' hW' hA'W'
      (fun h => hinfty h.1) (fun j hj x hx => hsingle j (Nat.lt_succ_of_lt hj) x ⟨hx.1.1, hx.2⟩)
      (fun a => Nbh ⟨a.val, a.property.1⟩) (fun a => hNbh _) (fun a => haNbh _)
    let P := Sum (Fin m) (Fin r)
    let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
    let D : P → ℂ ≃ₜ ℂ := Sum.elim H K
    let η : P → Circle → ℂ := Sum.elim γ δ
    have hDpair : Pairwise (Disjoint on fun p => closure (jordanInterior (D p))) := by
      intro p t hpt
      cases p with
      | inl i =>
        cases t with
        | inl j => exact hd (fun h => hpt (congrArg Sum.inl h))
        | inr j =>
          apply Set.disjoint_left.mpr
          intro z hzi hzj
          have hqC : q z ∈ C := mem_iUnion.mpr ⟨i, _, ⟨z, hzi, rfl⟩, rfl⟩
          exact ((hK j).1 hzj).2 (Or.inl hqC)
      | inr i =>
        cases t with
        | inl j =>
          apply Set.disjoint_left.mpr
          intro z hzi hzj
          have hqC : q z ∈ C := mem_iUnion.mpr ⟨j, _, ⟨z, hzj, rfl⟩, rfl⟩
          exact ((hK i).1 hzi).2 (Or.inl hqC)
        | inr j => exact hdK (fun h => hpt (congrArg Sum.inr h))
    refine ⟨Fintype.card P, (fun i => D (e.symm i)), (fun i => η (e.symm i)), ?_, ?_, ?_⟩
    · intro z hz
      by_cases hzU : q z ∈ U
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hzU
        have hzi : z ∈ jordanInterior (H i) := by
          rw [← physical_preimage_image_jordanInterior G π hsurj hr (H i)
            (fun w hw => (hb i w hw).1)]
          exact hi
        refine mem_iUnion.mpr ⟨e (Sum.inl i), ?_⟩
        simpa only [e.symm_apply_apply, D, Sum.elim_inl] using hzi
      · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcK ⟨hz, hzU⟩)
        refine mem_iUnion.mpr ⟨e (Sum.inr i), ?_⟩
        simpa only [e.symm_apply_apply, D, Sum.elim_inr] using hi
    · intro i j hij
      exact hDpair (fun h => hij (e.symm.injective h))
    · intro i
      change closure (jordanInterior (D (e.symm i))) ⊆ q ⁻¹' W ∧
        ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (η (e.symm i)) ∧
        Topology.IsEmbedding (η (e.symm i)) ∧
        frontier (jordanInterior (D (e.symm i))) = range (η (e.symm i)) ∧
        (∀ z ∈ frontier (jordanInterior (D (e.symm i))),
          (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B) ∧
        (∃ k : ℕ, ∀ j < n + 1, j ≠ k →
          Disjoint (frontier (jordanInterior (D (e.symm i)))) (q ⁻¹' J j)) ∧
        ∃ a : A, closure (jordanInterior (D (e.symm i))) ⊆ q ⁻¹' Nbh a
      generalize e.symm i = p
      cases p with
      | inl j =>
        dsimp only [D, η, Sum.elim_inl]
        refine ⟨(hcurves j).1, (hcurves j).2.1, (hcurves j).2.2.1,
          (hcurves j).2.2.2.1, hb j, ⟨n, ?_⟩, (hcurves j).2.2.2.2.2⟩
        intro k hk hkn
        apply Set.disjoint_left.mpr
        intro z hz hzk
        apply ((hcurves j).2.2.2.2.1 z hz).2
        exact Or.inr (mem_iUnion₂.mpr ⟨k,
          Finset.mem_range.mpr (lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkn), hzk⟩)
      | inr j =>
        dsimp only [D, η, Sum.elim_inr]
        obtain ⟨hinside, hsm, hemb, hfront, hav, ⟨k, hk⟩, a, ha⟩ := hK j
        refine ⟨(fun z hz => (hinside hz).1), hsm, hemb, hfront, hav, ⟨k, ?_⟩,
          ⟨a.val, a.property.1⟩, ha⟩
        intro t ht htk
        by_cases htn : t < n
        · exact hk t htn htk
        · have hteq : t = n := by omega
          subst t
          apply Set.disjoint_left.mpr
          intro z hz hzn
          exact (hinside (frontier_subset_closure hz)).2 (Or.inr hzn)

end CircleDomainRigidity

end OAI
