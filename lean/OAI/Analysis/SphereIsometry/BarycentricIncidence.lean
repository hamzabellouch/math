import OAI.Analysis.SphereIsometry.BarycentricFlags

namespace OAI

/-!
# Codimension-one incidence in the actual face-chain subdivision

Completions of a flag are counted by inserting its unique missing rank.
An interior missing rank has two completions. A missing top rank inherits
the incidence count of the greatest old face.
-/

noncomputable section

namespace Tingley.FiniteComplex

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : FiniteComplex V}

theorem chain_insert_iff {c : Finset (FaceVertex K)} {a : FaceVertex K} :
    K.chain (insert a c) ↔ K.chain c ∧
      ∀ b ∈ c, a.val ⊆ b.val ∨ b.val ⊆ a.val := by
  classical
  constructor
  · intro h
    exact ⟨K.chain_mono h (Finset.subset_insert _ _),
      fun b hb => h a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb)⟩
  · rintro ⟨hc, ha⟩ b hb d hd
    rcases Finset.mem_insert.mp hb with hba | hbc
    · subst b
      rcases Finset.mem_insert.mp hd with hda | hdc
      · subst d
        exact Or.inl (Finset.Subset.refl _)
      · exact ha d hdc
    · rcases Finset.mem_insert.mp hd with hda | hdc
      · subst d
        exact (ha b hbc).symm
      · exact hc b hbc d hdc

def insertionVertices (K : FiniteComplex V) (c : Finset (FaceVertex K)) :
    Finset (FaceVertex K) := by
  classical
  exact Finset.univ.filter (fun a => a ∉ c ∧ K.chain (insert a c))

@[simp] theorem mem_insertionVertices {c : Finset (FaceVertex K)} {a : FaceVertex K} :
    a ∈ K.insertionVertices c ↔ a ∉ c ∧ K.chain (insert a c) := by
  classical
  simp [insertionVertices]

theorem incidentTop_sd_eq_image_insert {m : ℕ} {c : Finset (FaceVertex K)}
    (hc : c.card = m) :
    K.sd.incidentTop m c = (K.insertionVertices c).image (fun a => insert a c) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨hdface, hdcard, hcd⟩ := mem_incidentTop.mp hd
    obtain ⟨a, ha, had⟩ := Finset.exists_eq_insert_iff.mpr
      (show c ⊆ d ∧ c.card + 1 = d.card from ⟨hcd, by omega⟩)
    apply Finset.mem_image.mpr
    refine ⟨a, mem_insertionVertices.mpr ⟨ha, ?_⟩, had⟩
    rw [had]
    exact mem_sd_iff.mp hdface
  · intro hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨ha, hchain⟩ := mem_insertionVertices.mp ha
    exact mem_incidentTop.mpr ⟨mem_sd_iff.mpr hchain,
      by rw [Finset.card_insert_of_notMem ha, hc], Finset.subset_insert _ _⟩

theorem incidentTop_sd_card_eq_insertionVertices {m : ℕ}
    {c : Finset (FaceVertex K)} (hc : c.card = m) :
    (K.sd.incidentTop m c).card = (K.insertionVertices c).card := by
  classical
  rw [incidentTop_sd_eq_image_insert hc]
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact (Finset.insert_inj (mem_insertionVertices.mp ha).1).mp hab

theorem rank_ne_of_missing {m r : ℕ} {c : Finset (FaceVertex K)}
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase r)
    {a : FaceVertex K} (ha : a ∈ c) : a.val.card ≠ r := by
  have h : a.val.card ∈ K.ranks c := mem_ranks.mpr ⟨a, ha, rfl⟩
  rw [hr] at h
  exact (Finset.mem_erase.mp h).1

theorem missing_rank_unique {m r s : ℕ} {c : Finset (FaceVertex K)}
    (hr₁ : 1 ≤ r) (hr₂ : r ≤ m + 1)
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase r)
    (hs : K.ranks c = (Finset.Icc 1 (m + 1)).erase s) : r = s := by
  by_contra hrs
  have hmem : r ∈ K.ranks c := by
    rw [hs]
    exact Finset.mem_erase.mpr ⟨hrs, Finset.mem_Icc.mpr ⟨hr₁, hr₂⟩⟩
  rw [hr] at hmem
  exact (Finset.mem_erase.mp hmem).1 rfl

theorem insertionVertices_card_eq_missing {m r : ℕ} (hK : K.CardBound m)
    {c : Finset (FaceVertex K)}
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase r)
    {a : FaceVertex K} (ha : a ∈ K.insertionVertices c) : a.val.card = r := by
  classical
  obtain ⟨hanot, hchain⟩ := mem_insertionVertices.mp ha
  by_contra har
  have hmem : a.val.card ∈ K.ranks c := by
    rw [hr]
    exact Finset.mem_erase.mpr ⟨har, Finset.mem_Icc.mpr
      ⟨Finset.card_pos.mpr a.property.2, hK a.val a.property.1⟩⟩
  obtain ⟨b, hb, hba⟩ := mem_ranks.mp hmem
  have hab : a = b := chain_eq_of_card_eq hchain (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem hb) hba.symm
  apply hanot
  rw [hab]
  exact hb

/-- Count possible inserted old faces between two consecutive retained ranks. -/
theorem card_insertionVertices_eq_sdiff {c : Finset (FaceVertex K)}
    {L U : Finset V} (hU : U ∈ K.faces) (hLU : L ⊆ U)
    (hmem : ∀ a : FaceVertex K, a ∈ K.insertionVertices c ↔
      L ⊆ a.val ∧ a.val ⊆ U ∧ a.val.card = L.card + 1) :
    (K.insertionVertices c).card = (U \ L).card := by
  classical
  let f : ∀ a ∈ U \ L, FaceVertex K := fun a ha =>
    ⟨insert a L,
      K.down_closed hU (Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp ha).1, hLU⟩),
      ⟨a, Finset.mem_insert_self _ _⟩⟩
  have hf : ∀ a ha, f a ha ∈ K.insertionVertices c := by
    intro a ha
    apply (hmem _).mpr
    exact ⟨Finset.subset_insert _ _,
      Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp ha).1, hLU⟩,
      Finset.card_insert_of_notMem (Finset.mem_sdiff.mp ha).2⟩
  have hinj : ∀ a ha b hb, f a ha = f b hb → a = b := by
    intro a ha b hb hab
    have heq : insert a L = insert b L := congrArg Subtype.val hab
    exact (Finset.insert_inj (Finset.mem_sdiff.mp ha).2).mp heq
  have hsurj : ∀ b ∈ K.insertionVertices c, ∃ a ha, f a ha = b := by
    intro b hb
    obtain ⟨hLb, hbU, hbcard⟩ := (hmem b).mp hb
    obtain ⟨a, haL, hab⟩ := Finset.exists_eq_insert_iff.mpr
      (show L ⊆ b.val ∧ L.card + 1 = b.val.card from ⟨hLb, hbcard.symm⟩)
    have haU : a ∈ U := by
      apply hbU
      rw [← hab]
      exact Finset.mem_insert_self _ _
    refine ⟨a, Finset.mem_sdiff.mpr ⟨haU, haL⟩, ?_⟩
    apply Subtype.ext
    exact hab
  exact (Finset.card_bij f hf hinj hsurj).symm

/-- An omitted rank strictly below the top has exactly two completions. -/
theorem incidentTop_sd_card_two_of_missing_rank {m r : ℕ} (hK : K.CardBound m)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.codimFaces m)
    (hr₁ : 1 ≤ r) (hrm : r ≤ m)
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase r) :
    (K.sd.incidentTop m c).card = 2 := by
  classical
  obtain ⟨hcface, hccard⟩ := mem_codimFaces.mp hc
  have hcchain := mem_sd_iff.mp hcface
  have hUr : r + 1 ∈ K.ranks c := by
    rw [hr]
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  obtain ⟨U, hUc, hUcard⟩ := mem_ranks.mp hUr
  obtain ⟨L, hLcard, hLU, hLmem, hgap⟩ :
      ∃ L : Finset V, L.card + 1 = r ∧ L ⊆ U.val ∧
        (L = ∅ ∨ ∃ a ∈ c, a.val = L) ∧
        ∀ b ∈ c, b.val ⊆ L ∨ U.val ⊆ b.val := by
    by_cases hrone : r = 1
    · refine ⟨∅, by simp [hrone], Finset.empty_subset _, Or.inl rfl, ?_⟩
      intro b hb
      right
      apply chain_subset_of_card_le hcchain hUc hb
      have hbpos := Finset.card_pos.mpr b.property.2
      have hbne := rank_ne_of_missing hr hb
      omega
    · have hLr : r - 1 ∈ K.ranks c := by
        rw [hr]
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
      obtain ⟨L, hLc, hLc_card⟩ := mem_ranks.mp hLr
      refine ⟨L.val, by omega,
        chain_subset_of_card_le hcchain hLc hUc (by omega),
        Or.inr ⟨L, hLc, rfl⟩, ?_⟩
      intro b hb
      have hbne := rank_ne_of_missing hr hb
      by_cases hbsmall : b.val.card ≤ L.val.card
      · exact Or.inl (chain_subset_of_card_le hcchain hb hLc hbsmall)
      · exact Or.inr (chain_subset_of_card_le hcchain hUc hb (by omega))
  have hmem : ∀ a : FaceVertex K, a ∈ K.insertionVertices c ↔
      L ⊆ a.val ∧ a.val ⊆ U.val ∧ a.val.card = L.card + 1 := by
    intro a
    constructor
    · intro ha
      have hacard := insertionVertices_card_eq_missing hK hr ha
      have hachain := (mem_insertionVertices.mp ha).2
      refine ⟨?_, chain_subset_of_card_le hachain (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem hUc) (by omega), by omega⟩
      rcases hLmem with hLempty | ⟨b, hbc, hbL⟩
      · rw [hLempty]
        exact Finset.empty_subset _
      · rw [← hbL]
        apply chain_subset_of_card_le hachain (Finset.mem_insert_of_mem hbc)
          (Finset.mem_insert_self _ _)
        have hbcard : b.val.card = L.card := congrArg Finset.card hbL
        omega
    · rintro ⟨hLa, haU, hacard⟩
      apply mem_insertionVertices.mpr
      refine ⟨?_, chain_insert_iff.mpr ⟨hcchain, ?_⟩⟩
      · intro hac
        exact rank_ne_of_missing hr hac (by omega)
      · intro b hb
        rcases hgap b hb with hbL | hUb
        · exact Or.inr (hbL.trans hLa)
        · exact Or.inl (haU.trans hUb)
  rw [incidentTop_sd_card_eq_insertionVertices hccard,
    card_insertionVertices_eq_sdiff U.property.1 hLU hmem,
    Finset.card_sdiff_of_subset hLU, hUcard]
  omega

/-- If the omitted rank is the top rank, completions are exactly the old
top faces containing the retained rank-`m` face. -/
theorem incidentTop_sd_card_eq_of_missing_top {m : ℕ} (hK : K.CardBound m)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.codimFaces m)
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase (m + 1))
    {T : FaceVertex K} (hTc : T ∈ c) (hTcard : T.val.card = m) :
    (K.sd.incidentTop m c).card = (K.incidentTop m T.val).card := by
  classical
  obtain ⟨hcface, hccard⟩ := mem_codimFaces.mp hc
  have hcchain := mem_sd_iff.mp hcface
  have hmax : ∀ b ∈ c, b.val ⊆ T.val := by
    intro b hb
    apply chain_subset_of_card_le hcchain hb hTc
    have hbcard := hK b.val b.property.1
    have hbne := rank_ne_of_missing hr hb
    omega
  let f : ∀ W ∈ K.incidentTop m T.val, FaceVertex K := fun W hW =>
    ⟨W, (mem_incidentTop.mp hW).1,
      Finset.card_pos.mp (by have h := (mem_incidentTop.mp hW).2.1; omega)⟩
  have hf : ∀ W hW, f W hW ∈ K.insertionVertices c := by
    intro W hW
    obtain ⟨hWface, hWcard, hTW⟩ := mem_incidentTop.mp hW
    apply mem_insertionVertices.mpr
    refine ⟨?_, chain_insert_iff.mpr ⟨hcchain, ?_⟩⟩
    · intro hWc
      have hle := Finset.card_le_card (hmax (f W hW) hWc)
      change W.card ≤ T.val.card at hle
      omega
    · intro b hb
      exact Or.inr ((hmax b hb).trans hTW)
  have hinj : ∀ W hW U hU, f W hW = f U hU → W = U := by
    intro W hW U hU h
    exact congrArg Subtype.val h
  have hsurj : ∀ a ∈ K.insertionVertices c,
      ∃ W hW, f W hW = a := by
    intro a ha
    have hacard := insertionVertices_card_eq_missing hK hr ha
    have hTa : T.val ⊆ a.val :=
      chain_subset_of_card_le (mem_insertionVertices.mp ha).2
        (Finset.mem_insert_of_mem hTc) (Finset.mem_insert_self _ _) (by omega)
    have hav : a.val ∈ K.incidentTop m T.val :=
      mem_incidentTop.mpr ⟨a.property.1, hacard, hTa⟩
    exact ⟨a.val, hav, Subtype.ext rfl⟩
  rw [incidentTop_sd_card_eq_insertionVertices hccard]
  exact (Finset.card_bij f hf hinj hsurj).symm

theorem incidentTop_sd_missing_top_data {m : ℕ} (hm : 0 < m) (hK : K.CardBound m)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.codimFaces m)
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase (m + 1)) :
    ∃ T ∈ c, T.val.card = m ∧ (∀ b ∈ c, b.val ⊆ T.val) ∧
      (K.sd.incidentTop m c).card = (K.incidentTop m T.val).card := by
  have hmrank : m ∈ K.ranks c := by
    rw [hr]
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨hm, by omega⟩⟩
  obtain ⟨T, hTc, hTcard⟩ := mem_ranks.mp hmrank
  refine ⟨T, hTc, hTcard, ?_, incidentTop_sd_card_eq_of_missing_top hK hc hr hTc hTcard⟩
  intro b hb
  apply chain_subset_of_card_le (mem_sd_iff.mp (mem_codimFaces.mp hc).1) hb hTc
  have hbcard := hK b.val b.property.1
  have hbne := rank_ne_of_missing hr hb
  omega

/-- The complete positive-dimensional codimension-one alternative. The first
case also records a retained old top face for transferring carrier information. -/
theorem incidentTop_sd_cases {m : ℕ} (hm : 0 < m) (hK : K.CardBound m)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.codimFaces m) :
    ((K.sd.incidentTop m c).card = 2 ∧
      ∃ T ∈ c, T.val.card = m + 1 ∧ ∀ b ∈ c, b.val ⊆ T.val) ∨
    (∃ T ∈ c, T.val.card = m ∧ (∀ b ∈ c, b.val ⊆ T.val) ∧
      (K.sd.incidentTop m c).card = (K.incidentTop m T.val).card) := by
  obtain ⟨r, hr₁, hr₂, hr⟩ := missing_rank hK hc
  by_cases hrm : r ≤ m
  · left
    refine ⟨incidentTop_sd_card_two_of_missing_rank hK hc hr₁ hrm hr, ?_⟩
    have hmrank : m + 1 ∈ K.ranks c := by
      rw [hr]
      exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩⟩
    obtain ⟨T, hTc, hTcard⟩ := mem_ranks.mp hmrank
    refine ⟨T, hTc, hTcard, ?_⟩
    intro b hb
    apply chain_subset_of_card_le (mem_sd_iff.mp (mem_codimFaces.mp hc).1) hb hTc
    rw [hTcard]
    exact hK b.val b.property.1
  · right
    have hre : r = m + 1 := by omega
    subst r
    exact incidentTop_sd_missing_top_data hm hK hc hr

end Tingley.FiniteComplex

end

end OAI
