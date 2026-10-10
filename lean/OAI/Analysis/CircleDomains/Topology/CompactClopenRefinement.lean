import OAI.Analysis.CircleDomains.Selection.DustCover

namespace OAI

/-!
# Finite clopen partitions subordinate to prescribed dust neighborhoods

This retains the compact pieces and their containment data, rather than only
the open cover returned by `DustCover`. They are the pieces pulled back to the
physical sphere before simultaneous smooth contour construction.
-/

open Set Function TopologicalSpace

namespace CircleDomainRigidity

theorem exists_compact_clopen_refinement
    {X : Type*} [TopologicalSpace X] [T2Space X] {B : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    (V : B → Set X) (hV : ∀ b, IsOpen (V b)) (hbV : ∀ b, b.val ∈ V b) :
    ∃ (n : ℕ) (A : Fin n → Set X) (b : Fin n → B),
      (∀ i, IsCompact (A i) ∧ A i ⊆ B ∧ A i ⊆ V (b i) ∧ IsClosed (B \ A i)) ∧
      Pairwise (Disjoint on A) ∧ (⋃ i, A i) = B := by
  classical
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let : TotallyDisconnectedSpace B := totallyDisconnectedSpace_subtype_iff.mpr hTD
  let O : B → Opens B := fun b => ⟨Subtype.val ⁻¹' V b,
    (hV b).preimage continuous_subtype_val⟩
  have hO : IsOpenCover O := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro b
    exact mem_iUnion.mpr ⟨b, hbV b⟩
  obtain ⟨n, C, hC, hcover, hdisj⟩ := hO.exists_finite_nonempty_disjoint_clopen_cover
  choose b hb using fun i => (hC i).2
  let A : Fin n → Set X := fun i => Subtype.val '' (C i : Set B)
  have hAB (i) : A i ⊆ B := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hdiff (i) : B \ A i = Subtype.val '' ((C i : Set B)ᶜ) := by
    ext x
    constructor
    · rintro ⟨hx, hxA⟩
      exact ⟨⟨x, hx⟩, fun h => hxA ⟨⟨x, hx⟩, h, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.property, ?_⟩
      rintro ⟨y, hy, hyx⟩
      exact hx (Subtype.ext hyx ▸ hy)
  refine ⟨n, A, b, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(C i).isClosed.isCompact.image continuous_subtype_val, hAB i, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hb i hx
    · rw [hdiff]
      exact hB.isClosed.isClosedMap_subtype_val _ (C i).isOpen.isClosed_compl
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
    have hvu' : v = u := Subtype.ext hvu
    subst v
    exact Set.disjoint_left.mp (Clopens.coe_disjoint.mpr (hdisj hij)) hu hv
  · apply Set.Subset.antisymm (iUnion_subset hAB)
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_univ (⟨x, hx⟩ : B)))
    exact mem_iUnion.mpr ⟨i, ⟨x, hx⟩, hi, rfl⟩

end CircleDomainRigidity

end OAI
