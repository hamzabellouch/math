import OAI.Probability.MatroidProphet.Pivots.Blocks

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α A T : Type*} [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T] {n : ℕ}

def blockLabel (F : T → Set α) (a : A → α) : BlockOld F ⊕ A → α :=
  Sum.elim (blockOldLabel (F := F)) a

def blockPrefix (F : T → Set α) (a : A → α) (τ : A → T) (k : T) : Set α :=
  blockLabel F a '' {o | blockStage F τ o ≤ k}

def blockBefore (F : T → Set α) (a : A → α) (τ : A → T) (k : T) : Set α :=
  blockLabel F a '' {o | blockStage F τ o < k}

noncomputable def blockBirthPattern (M : Matroid α) (F : T → Set α)
    (a : A → α) (τ : A → T) (test : Fin n → α) (mark : T → Bool) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => ∃ k, mark k = true ∧
    test f ∈ M.closure (blockPrefix F a τ k) ∧ test f ∉ M.closure (blockBefore F a τ k)

lemma pivot_block_birth (M : Matroid α) (F : T → Set α) (a : A → α)
    (τ : A → T) {e : α} {o : BlockOld F ⊕ A}
    (hp : IsPivot M (blockLabel F a) (blockTime F τ) e o) :
    e ∈ M.closure (blockPrefix F a τ (blockStage F τ o)) ∧
      e ∉ M.closure (blockBefore F a τ (blockStage F τ o)) := by
  constructor
  · apply M.closure_subset_closure (Set.image_mono ?_) hp.1
    exact fun p h => blockTime_le_implies_stage_le F τ h
  · intro h
    apply hp.2
    apply M.closure_subset_closure (Set.image_mono ?_) h
    exact fun p h => stage_lt_implies_blockTime_lt F τ h

lemma block_birth_unique
    {α : Type u_1} {A : Type u_2} {T : Type u_3}
    [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]
    (M : Matroid α) (F : T → Set α) (a : A → α)
    (τ : A → T) {e : α} {k l : T}
    (hk : e ∈ M.closure (blockPrefix F a τ k) ∧ e ∉ M.closure (blockBefore F a τ k))
    (hl : e ∈ M.closure (blockPrefix F a τ l) ∧ e ∉ M.closure (blockBefore F a τ l)) :
    k = l := by
  rcases lt_trichotomy k l with h | rfl | h
  · exact (hl.2 (M.closure_subset_closure (Set.image_mono (fun _ hx => lt_of_le_of_lt hx h)) hk.1)).elim
  · rfl
  · exact (hk.2 (M.closure_subset_closure (Set.image_mono (fun _ hx => lt_of_le_of_lt hx h)) hl.1)).elim

lemma blockBirthPattern_mem_freeMarkedPatterns (M : Matroid α) (F : T → Set α)
    (a : A → α) (τ : A → T) (test : Fin n → α) (mark : T → Bool)
    (hnonloop : ∀ f, test f ∉ M.closure ∅)
    (hspan : ∀ f, test f ∈ M.closure (Set.range (blockLabel F a))) :
    blockBirthPattern M F a τ test mark ∈
      freeMarkedPatterns M (blockOldLabel (F := F)) a test (fun o : BlockOld F => mark (blockOldStage (F := F) o)) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, blockTime F τ, blockTime_old_strictMono F τ,
    blockTime_injective F τ, mark ∘ τ, ?_⟩
  intro f
  obtain ⟨o, hp⟩ := exists_pivot M (blockLabel F a) (blockTime F τ) (hnonloop f) (hspan f)
  refine ⟨o, hp, ?_⟩
  have hb := pivot_block_birth M F a τ hp
  change Sum.elim (fun o : BlockOld F => mark (blockOldStage (F := F) o)) (mark ∘ τ) o = true ↔ _
  have hm : Sum.elim (fun o : BlockOld F => mark (blockOldStage (F := F) o)) (mark ∘ τ) o =
      mark (blockStage F τ o) := by cases o <;> rfl
  rw [hm]
  simp only [blockBirthPattern, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨blockStage F τ o, h, hb⟩
  · rintro ⟨k, hmark, hk⟩
    have heq := block_birth_unique M F a τ hb hk
    simpa only [heq] using hmark

lemma blockPrefix_eq
    {α : Type u_1} {A : Type u_2} {T : Type u_3}
    [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]
    (F : T → Set α) (hF : Monotone F)
    (a : A → α) (τ : A → T) (k : T) :
    blockPrefix F a τ k = F k ∪ a '' {g | τ g ≤ k} := by
  ext e
  constructor
  · rintro ⟨o, ho, rfl⟩
    cases o with
    | inl o => exact Or.inl (hF ho o.property)
    | inr g => exact Or.inr ⟨g, ho, rfl⟩
  · rintro (he | ⟨g, hg, rfl⟩)
    · exact ⟨Sum.inl ⟨toLex (k, e), he⟩, by change k ≤ k; exact le_rfl, rfl⟩
    · exact ⟨Sum.inr g, hg, rfl⟩

lemma blockBefore_eq_iUnion
    {α : Type u_1} {A : Type u_2} {T : Type u_3}
    [Fintype α] [LinearOrder α] [Fintype A] [Fintype T] [LinearOrder T]
    (F : T → Set α) (a : A → α) (τ : A → T)
    (k : T) :
    blockBefore F a τ k = (⋃ j : T, ⋃ (_ : j < k), F j) ∪ a '' {g | τ g < k} := by
  ext e
  constructor
  · rintro ⟨o, ho, rfl⟩
    cases o with
    | inl o => exact Or.inl (mem_iUnion.mpr ⟨blockOldStage (F := F) o, mem_iUnion.mpr ⟨ho, o.property⟩⟩)
    | inr g => exact Or.inr ⟨g, ho, rfl⟩
  · rintro (he | ⟨g, hg, rfl⟩)
    · obtain ⟨j, hj, he⟩ := mem_iUnion.mp he |>.imp fun _ h => mem_iUnion.mp h
      exact ⟨Sum.inl ⟨toLex (j, e), he⟩, hj, rfl⟩
    · exact ⟨Sum.inr g, hg, rfl⟩

end MatroidProphet.Pivots

end OAI
