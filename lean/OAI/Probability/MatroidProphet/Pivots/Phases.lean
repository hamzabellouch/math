import OAI.Probability.MatroidProphet.Pivots.BlockPatterns

namespace OAI

namespace MatroidProphet.Pivots

open Set

variable {α G Z B : Type*} [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z]
    [Fintype B] [LinearOrder B]

def phaseOld (F K : B → Set α) (p : B ×ₗ Bool) : Set α :=
  if (ofLex p).2 then F (ofLex p).1 else K (ofLex p).1

def phasePlacement (θ : G → B) (β : Z → B) : G ⊕ Z → B ×ₗ Bool :=
  Sum.elim (fun g => toLex (θ g, true)) (fun z => toLex (β z, false))

def upperPath (M : Matroid α) (F : B → Set α) (a : G → α) (θ : G → B) (b : B) : Set α :=
  M.closure (F b ∪ a '' {g | θ g ≤ b})

def lowerPath (M : Matroid α) (F : B → Set α) (a : G → α) (θ : G → B) (b : B) : Set α :=
  M.closure ((⋃ c, ⋃ (_ : c < b), F c) ∪ a '' {g | θ g < b})

lemma upperPath_mono
    {α : Type u_1} {G : Type u_2} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype B] [LinearOrder B]
    (M : Matroid α) (F : B → Set α) (hF : Monotone F)
    (a : G → α) (θ : G → B) : Monotone (upperPath M F a θ) := by
  intro b c hbc
  exact M.closure_subset_closure (union_subset_union (hF hbc)
    (image_mono (fun _ hx => hx.trans hbc)))

lemma upperPath_subset_lowerPath
    {α : Type u_1} {G : Type u_2} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype B] [LinearOrder B]
    (M : Matroid α) (F : B → Set α)
    (a : G → α) (θ : G → B) {b c : B} (hbc : b < c) :
    upperPath M F a θ b ⊆ lowerPath M F a θ c := by
  apply M.closure_subset_closure
  apply union_subset_union
  · exact fun e he => mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hbc, he⟩⟩
  · exact image_mono (fun _ hx => lt_of_le_of_lt hx hbc)

lemma phase_prefix_end_eq
    {α : Type u_1} {G : Type u_2} {Z : Type u_3} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z] [Fintype B] [LinearOrder B]
    (F K : B → Set α) (hF : Monotone F) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B) (b : B) :
    blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, true)) =
      (F b ∪ a '' {g | θ g ≤ b}) ∪ z '' {w | β w ≤ b} := by
  ext e
  constructor
  · rintro ⟨o, ho, rfl⟩
    cases o with
    | inl o =>
      have hc : (ofLex (blockOldStage (F := phaseOld F K) o)).1 ≤ b := by
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        exact ht.elim le_of_lt (fun h => h.1.le)
      have hl : blockOldLabel (F := phaseOld F K) o ∈ F (ofLex (blockOldStage (F := phaseOld F K) o)).1 := by
        have hp := o.property
        change blockOldLabel (F := phaseOld F K) o ∈ phaseOld F K (blockOldStage (F := phaseOld F K) o) at hp
        unfold phaseOld at hp
        split at hp
        · exact hp
        · exact hK _ hp
      exact Or.inl (Or.inl (hF hc hl))
    | inr o =>
      cases o with
      | inl g =>
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        exact Or.inl (Or.inr ⟨g, ht.elim le_of_lt (fun h => h.1.le), rfl⟩)
      | inr w =>
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        exact Or.inr ⟨w, ht.elim le_of_lt (fun h => h.1.le), rfl⟩
  · rintro ((he | ⟨g, hg, rfl⟩) | ⟨w, hw, rfl⟩)
    · refine ⟨Sum.inl ⟨toLex (toLex (b, true), e), he⟩, ?_, rfl⟩
      change toLex (b, true) ≤ toLex (b, true)
      exact le_rfl
    · refine ⟨Sum.inr (Sum.inl g), ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr ((lt_or_eq_of_le hg).imp id (fun h => ⟨h, le_rfl⟩))
    · refine ⟨Sum.inr (Sum.inr w), ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr ((lt_or_eq_of_le hw).imp id (fun h => ⟨h, show (false : Bool) ≤ true from by decide⟩))

lemma phase_endpoint (M : Matroid α) (hE : M.E = univ)
    (F K : B → Set α) (hF : Monotone F) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B)
    (hz : ∀ w, z w ∈ upperPath M F a θ (β w)) (b : B) :
    M.closure (blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, true))) =
      upperPath M F a θ b := by
  rw [phase_prefix_end_eq F K hF hK]
  apply Subset.antisymm
  · apply (M.closure_subset_closure ?_).trans_eq (M.closure_closure _)
    apply union_subset
    · exact M.subset_closure _ (by simp [hE])
    · rintro _ ⟨w, hw, rfl⟩
      exact upperPath_mono M F hF a θ hw (hz w)
  · exact M.closure_subset_closure subset_union_left

lemma phase_prefix_interior_eq
    {α : Type u_1} {G : Type u_2} {Z : Type u_3} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z] [Fintype B] [LinearOrder B]
    (F K : B → Set α) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B) (b : B) :
    blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, false)) =
      (((⋃ c, ⋃ (_ : c < b), F c) ∪ a '' {g | θ g < b}) ∪ K b) ∪ z '' {w | β w ≤ b} := by
  ext e
  constructor
  · rintro ⟨o, ho, rfl⟩
    cases o with
    | inl o =>
      have ht := Prod.Lex.toLex_le_toLex.mp ho
      have hp := o.property
      change blockOldLabel (F := phaseOld F K) o ∈ phaseOld F K (blockOldStage (F := phaseOld F K) o) at hp
      rcases ht with hc | ⟨hc, hb⟩
      · left; left; left
        refine mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨hc, ?_⟩⟩
        unfold phaseOld at hp
        split at hp
        · exact hp
        · exact hK _ hp
      · left; right
        have hf : (ofLex (blockOldStage (F := phaseOld F K) o)).2 = false := by
          change (ofLex (blockOldStage (F := phaseOld F K) o)).2 ≤ false at hb
          exact le_antisymm hb bot_le
        change (ofLex (blockOldStage (F := phaseOld F K) o)).1 = b at hc
        change blockOldLabel (F := phaseOld F K) o ∈ K b
        simpa [phaseOld, hf, hc] using hp
    | inr o =>
      cases o with
      | inl g =>
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        have hg : θ g < b := ht.elim id (fun h => by have hh : false = true := h.2 rfl; cases hh)
        exact Or.inl (Or.inl (Or.inr ⟨g, hg, rfl⟩))
      | inr w =>
        have ht := Prod.Lex.toLex_le_toLex.mp ho
        exact Or.inr ⟨w, ht.elim le_of_lt (fun h => h.1.le), rfl⟩
  · rintro (((he | ⟨g, hg, rfl⟩) | hk) | ⟨w, hw, rfl⟩)
    · obtain ⟨c, hc, he⟩ := mem_iUnion.mp he |>.imp fun _ h => mem_iUnion.mp h
      refine ⟨Sum.inl ⟨toLex (toLex (c, true), e), he⟩, ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inl hc)
    · refine ⟨Sum.inr (Sum.inl g), ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inl hg)
    · refine ⟨Sum.inl ⟨toLex (toLex (b, false), e), hk⟩, ?_, rfl⟩
      change toLex (b, false) ≤ toLex (b, false)
      exact le_rfl
    · refine ⟨Sum.inr (Sum.inr w), ?_, rfl⟩
      exact Prod.Lex.toLex_le_toLex.mpr ((lt_or_eq_of_le hw).imp id (fun h => ⟨h, le_rfl⟩))

lemma phase_interior (M : Matroid α) (hE : M.E = univ)
    (F K : B → Set α) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B)
    (hz : ∀ w, z w ∈ upperPath M F a θ (β w)) (b : B) :
    M.closure (blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, false))) =
      M.closure (lowerPath M F a θ b ∪ K b ∪ z '' {w | β w = b}) := by
  rw [phase_prefix_interior_eq F K hK]
  apply Subset.antisymm
  · apply (M.closure_subset_closure ?_).trans_eq (M.closure_closure _)
    rintro e ((he | hk) | ⟨w, hw, rfl⟩)
    · apply M.subset_closure _ (by simp [hE])
      exact Or.inl (Or.inl (M.subset_closure _ (by simp [hE]) he))
    · exact M.subset_closure _ (by simp [hE]) (Or.inl (Or.inr hk))
    · rcases lt_or_eq_of_le hw with hw | hw
      · apply M.subset_closure _ (by simp [hE])
        exact Or.inl (Or.inl (upperPath_subset_lowerPath M F a θ hw (hz w)))
      · exact M.subset_closure _ (by simp [hE]) (Or.inr ⟨w, hw, rfl⟩)
  · rw [union_assoc (lowerPath M F a θ b), lowerPath, M.closure_union_closure_left_eq, ← union_assoc]
    apply M.closure_subset_closure
    exact union_subset_union Subset.rfl (image_mono (fun _ h => h.le))

end MatroidProphet.Pivots

end OAI
