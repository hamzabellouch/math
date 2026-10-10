import OAI.Combinatorics.BalancedRyser.Probability.CoreRepresentatives

namespace OAI

namespace Balanced.Configuration

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

omit [Field F] in
theorem eq_of_common_coreRepresentative
    {b c : BlockLabel F} (hb : C.IsBlockLabel b) (hc : C.IsBlockLabel c)
    {l : Line F} (hlb : l ∈ C.coreRepresentative b)
    (hlc : l ∈ C.coreRepresentative c) : b = c := by
  rcases b with m | d | s <;> rcases c with n | e | t
  · simp only [coreRepresentative, Finset.mem_singleton] at hlb hlc
    exact congrArg Sum.inl (hlb.symm.trans hlc)
  · simp only [coreRepresentative, Finset.mem_singleton] at hlb hlc
    have hm : m = constituent C.merged e false := hlb.symm.trans hlc
    exact False.elim (hb (Finset.mem_union_right _
      (hm.symm ▸ C.mem_constituentLines e false)))
  · simp [coreRepresentative] at hlc
  · simp only [coreRepresentative, Finset.mem_singleton] at hlb hlc
    have hn : n = constituent C.merged d false := hlc.symm.trans hlb
    exact False.elim (hc (Finset.mem_union_right _
      (hn.symm ▸ C.mem_constituentLines d false)))
  · simp only [coreRepresentative, Finset.mem_singleton] at hlb hlc
    have hde : d = e := congrArg Prod.fst (hlb.symm.trans hlc)
    exact congrArg (fun x => Sum.inr (Sum.inl x)) hde
  · simp [coreRepresentative] at hlc
  · simp [coreRepresentative] at hlb
  · simp [coreRepresentative] at hlb
  · simp [coreRepresentative] at hlb

omit [Field F] in
theorem coreRepresentative_disjoint
    {b c : BlockLabel F} (hb : C.IsBlockLabel b) (hc : C.IsBlockLabel c)
    (hbc : b ≠ c) : Disjoint (C.coreRepresentative b) (C.coreRepresentative c) := by
  apply Finset.disjoint_left.mpr
  intro l hlb hlc
  exact hbc (C.eq_of_common_coreRepresentative hb hc hlb hlc)

theorem filtered_representatives_card_eq
    (B : Finset (BlockLabel F)) (hB : ∀ b ∈ B, C.IsBlockLabel b)
    (E : Line F → Prop) :
    ((B.biUnion C.coreRepresentative).filter E).card =
      (B.filter (fun b => ∃ l ∈ C.coreRepresentative b, E l)).card := by
  classical
  have hfilter : (B.biUnion C.coreRepresentative).filter E =
      B.biUnion (fun b => (C.coreRepresentative b).filter E) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    aesop
  rw [hfilter, Finset.card_biUnion]
  · rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro b hb
    rcases b with l | d | s
    · by_cases h : E l <;> simp [coreRepresentative, Finset.filter_singleton, h]
    · by_cases h : E (constituent C.merged d false) <;>
        simp [coreRepresentative, Finset.filter_singleton, h]
    · simp [coreRepresentative]
  · intro b hb c hc hbc
    exact (C.coreRepresentative_disjoint (hB b hb) (hB c hc) hbc).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem representatives_card_eq_nonempty
    (B : Finset (BlockLabel F)) (hB : ∀ b ∈ B, C.IsBlockLabel b) :
    (B.biUnion C.coreRepresentative).card =
      (B.filter (fun b => (C.coreRepresentative b).Nonempty)).card := by
  classical
  have hcard := C.filtered_representatives_card_eq B hB (fun _ => True)
  rw [Finset.filter_true] at hcard
  refine hcard.trans ?_
  congr 1
  ext label
  simp only [Finset.mem_filter]
  simp only [Finset.Nonempty, and_true]

theorem pencil_representatives_card_eq_labels
    (B : Finset (BlockLabel F)) (hB : ∀ b ∈ B, C.IsBlockLabel b)
    (P : ProjectivePoint F) :
    ((B.biUnion C.coreRepresentative).filter (fun l => ThroughProjective l P)).card =
      (B.filter (C.RepresentedThrough P)).card := by
  classical
  have h := C.filtered_representatives_card_eq B hB (fun l => ThroughProjective l P)
  convert h using 1
  · congr 1
    ext l
    simp only [Finset.mem_filter]
  · congr 1
    ext b
    simp only [Finset.mem_filter, RepresentedThrough]

theorem core_block_mem_iff_representative
    (hV : C.Valid) {b : BlockLabel F} (hb : C.IsBlockLabel b)
    {p : Point F} (hp : p ∈ C.core) :
    p ∈ C.blockPoints b ↔ ∃ l ∈ C.coreRepresentative b, OnLine p l := by
  constructor
  · intro hpb
    obtain ⟨l, hl, _, hpl⟩ := C.core_block_has_representative hV hb hp hpb
    exact ⟨l, hl, hpl⟩
  · rintro ⟨l, hl, hpl⟩
    have hX := C.core_subset_points_for_representatives hp
    have hlp : p ∈ linePoints l := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩
    rcases b with m | d | s
    · simp only [coreRepresentative, Finset.mem_singleton] at hl
      exact Finset.mem_inter.mpr ⟨hl ▸ hlp, hX⟩
    · simp only [coreRepresentative, Finset.mem_singleton] at hl
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (hl ▸ hlp), hX⟩
    · simp [coreRepresentative] at hl

theorem core_cover_iff_representative_cover
    (hV : C.Valid) (B : Finset (BlockLabel F))
    (hB : ∀ b ∈ B, C.IsBlockLabel b) :
    C.core ⊆ B.biUnion C.blockPoints ↔
      CoversPoints (B.biUnion C.coreRepresentative) C.core := by
  constructor
  · intro h p hp
    obtain ⟨b, hb, hpb⟩ := Finset.mem_biUnion.mp (h hp)
    obtain ⟨l, hl, hpl⟩ := (C.core_block_mem_iff_representative hV (hB b hb) hp).mp hpb
    exact ⟨l, Finset.mem_biUnion.mpr ⟨b, hb, hl⟩, hpl⟩
  · intro h p hp
    obtain ⟨l, hl, hpl⟩ := h p hp
    obtain ⟨b, hb, hbl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_biUnion.mpr ⟨b, hb,
      (C.core_block_mem_iff_representative hV (hB b hb) hp).mpr ⟨l, hbl, hpl⟩⟩

omit [Field F] in
theorem existsUnique_label_of_not_deleted
    {l : Line F} (hl : l ∉ C.deletedLines) :
    ∃! b : BlockLabel F, C.IsBlockLabel b ∧ l ∈ C.coreRepresentative b := by
  classical
  have hex : ∃ b : BlockLabel F, C.IsBlockLabel b ∧ l ∈ C.coreRepresentative b := by
    by_cases hc : l ∈ constituentLines C.merged
    · obtain ⟨⟨d, s⟩, _, rfl⟩ := Finset.mem_image.mp hc
      cases s
      · exact ⟨Sum.inr (Sum.inl d), trivial, Finset.mem_singleton_self _⟩
      · exact False.elim (hl (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩)))
    · refine ⟨Sum.inl l, ?_, Finset.mem_singleton_self _⟩
      intro hbad
      rcases Finset.mem_union.mp hbad with hs | hc'
      · exact hl (Finset.mem_union_left _ hs)
      · exact hc hc'
  obtain ⟨b, hb, hlb⟩ := hex
  exact ⟨b, ⟨hb, hlb⟩, fun c hc =>
    C.eq_of_common_coreRepresentative hc.1 hb hc.2 hlb⟩

theorem all_coreRepresentatives_eq_nondeleted (hV : C.Valid) :
    C.blockLabels.biUnion C.coreRepresentative = Finset.univ \ C.deletedLines := by
  classical
  ext l
  constructor
  · intro hl
    obtain ⟨b, hb, hbl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      C.coreRepresentative_not_deleted hV (Finset.mem_filter.mp hb).2 hbl⟩
  · intro hl
    obtain ⟨b, ⟨hb, hbl⟩, _⟩ := C.existsUnique_label_of_not_deleted
      (Finset.mem_sdiff.mp hl).2
    exact Finset.mem_biUnion.mpr ⟨b,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, hbl⟩

end
end Balanced.Configuration

end OAI
