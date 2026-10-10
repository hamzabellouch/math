import OAI.Analysis.CircleDomains.Selection.DustCover

namespace OAI

/-! Finite small disjoint dust neighborhoods inside a prescribed safe open
set. Empty dust pieces are discarded, and every boundary avoids all dust. -/

open Set Metric Function Filter
open scoped Topology

namespace CircleDomainRigidity

theorem exists_safe_small_dust_cover
    {X : Type*} [MetricSpace X] [CompactSpace X]
    {B W : Set X} (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    (hW : IsOpen W) (hBW : B ⊆ W) {ε : ℝ} (hε : 0 < ε) :
    ∃n : ℕ, ∃V : Fin n → Set X,
      (∀i, IsOpen (V i)) ∧ B ⊆ ⋃i, V i ∧
      Pairwise (Disjoint on fun i => closure (V i)) ∧
      (∀i, closure (V i) ⊆ W) ∧
      (∀i, diam (V i) < ε) ∧
      (∀i, (V i ∩ B).Nonempty) ∧
      (∀i, Disjoint (frontier (V i)) B) := by
  classical
  obtain ⟨A, hAo, hBA, hAW⟩ := hB.exists_isOpen_closure_subset (hW.mem_nhdsSet.mpr hBW)
  obtain ⟨n, U, hUo, hBU, hUd, hdiam⟩ :=
    exists_small_disjoint_open_cover_of_compact_dust hB hTD hε
  let V₀ : Fin n → Set X := fun i => U i ∩ A
  let J := {i : Fin n // (V₀ i ∩ B).Nonempty}
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let V : Fin (Fintype.card J) → Set X := fun i => V₀ (e.symm i).val
  have hsub (i : Fin (Fintype.card J)) : closure (V i) ⊆ closure (U (e.symm i).val) :=
    closure_mono inter_subset_left
  have hcover : B ⊆ ⋃i, V i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hBU hx)
    let j : J := ⟨i, ⟨x, ⟨hi, hBA hx⟩, hx⟩⟩
    exact mem_iUnion.mpr ⟨e j, by simpa only [V, e.symm_apply_apply] using (show x ∈ V₀ i from ⟨hi, hBA hx⟩)⟩
  have hpair : Pairwise (Disjoint on fun i => closure (V i)) := by
    intro i j hij
    apply (hUd (show (e.symm i).val ≠ (e.symm j).val from ?_)).mono (hsub i) (hsub j)
    intro h
    exact hij (e.symm.injective (Subtype.ext h))
  refine ⟨Fintype.card J, V, fun i => (hUo _).inter hAo, hcover, hpair, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (closure_mono (show V i ⊆ A from inter_subset_right)).trans hAW
  · intro i
    exact (diam_mono ((subset_closure : V i ⊆ closure (V i)).trans (hsub i))
      (isClosed_closure.isCompact.isBounded)).trans_lt (hdiam _)
  · intro i
    exact (e.symm i).property
  · intro i
    apply Set.disjoint_left.mpr
    intro x hx hxB
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hxB)
    by_cases hij : i = j
    · subst j
      have hVo : IsOpen (V i) := (hUo _).inter hAo
      rw [hVo.frontier_eq] at hx
      exact hx.2 hj
    · exact Set.disjoint_left.mp (hpair hij) (frontier_subset_closure hx) (subset_closure hj)

end CircleDomainRigidity

end OAI
