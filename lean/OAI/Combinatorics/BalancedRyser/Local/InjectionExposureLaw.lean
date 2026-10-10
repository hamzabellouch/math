import OAI.Combinatorics.BalancedRyser.Probability.PermutationSubsetLaw

namespace OAI

open scoped BigOperators

namespace Balanced.InjectionExposureLaw

noncomputable section

variable {ι α : Type*} [Fintype ι] [Fintype α]
  [DecidableEq ι] [DecidableEq α]

def history (S : Finset ι) (h : ι ↪ α) : Finset (ι ↪ α) :=
  Finset.univ.filter fun f => ∀ j ∈ S, f j = h j

def available (S : Finset ι) (h : ι ↪ α) : Finset α :=
  Finset.univ \ S.map h

@[simp] theorem mem_history (S : Finset ι) (h f : ι ↪ α) :
    f ∈ history S h ↔ ∀ j ∈ S, f j = h j := by simp [history]

@[simp] theorem self_mem_history (S : Finset ι) (h : ι ↪ α) :
    h ∈ history S h := by simp

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem mem_available (S : Finset ι) (h : ι ↪ α) (x : α) :
    x ∈ available S h ↔ x ∉ S.map h := by simp [available]

def postcompose (τ : Equiv.Perm α) : (ι ↪ α) ≃ (ι ↪ α) where
  toFun f := f.trans τ.toEmbedding
  invFun f := f.trans τ.symm.toEmbedding
  left_inv f := by ext j; simp
  right_inv f := by ext j; simp

omit [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α] in
@[simp] theorem postcompose_apply (τ : Equiv.Perm α) (f : ι ↪ α) (j : ι) :
    postcompose τ f j = τ (f j) := rfl

theorem next_fiber_card_eq (S : Finset ι) (h : ι ↪ α) (i : ι)
    (a b : α) (ha : a ∈ available S h) (hb : b ∈ available S h) :
    ((history S h).filter (fun f => f i = a)).card =
      ((history S h).filter (fun f => f i = b)).card := by
  classical
  let τ := Equiv.swap a b
  have hfix (j : ι) (hj : j ∈ S) : τ (h j) = h j := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro heq
      exact (mem_available S h a).mp ha (heq ▸ Finset.mem_map.mpr ⟨j, hj, rfl⟩)
    · intro heq
      exact (mem_available S h b).mp hb (heq ▸ Finset.mem_map.mpr ⟨j, hj, rfl⟩)
  apply Finset.card_equiv (postcompose τ)
  intro f
  simp only [Finset.mem_filter, mem_history, postcompose_apply]
  constructor
  · rintro ⟨hf, hfi⟩
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [hf j hj, hfix j hj]
    · simp [τ, hfi]
  · rintro ⟨hf, hfi⟩
    refine ⟨fun j hj => ?_, ?_⟩
    · apply τ.injective
      exact (hf j hj).trans (hfix j hj).symm
    · apply τ.injective
      simpa [τ] using hfi

theorem next_mem_available (S : Finset ι) (h f : ι ↪ α) (i : ι)
    (hi : i ∉ S) (hf : f ∈ history S h) : f i ∈ available S h := by
  rw [mem_available]
  intro he
  obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp he
  have hfj : f j = f i := ((mem_history S h f).mp hf j hj).trans hji
  exact hi ((f.injective hfj) ▸ hj)

theorem expect_next_given_history (S : Finset ι) (h : ι ↪ α) (i : ι)
    (hi : i ∉ S) (g : α → ℝ) :
    (𝔼 f ∈ history S h, g (f i)) = 𝔼 x ∈ available S h, g x := by
  let m := ((history S h).filter (fun f => f i = h i)).card
  have hm : 0 < m := Finset.card_pos.mpr
    ⟨h, Finset.mem_filter.mpr ⟨self_mem_history S h, rfl⟩⟩
  apply PermutationSubsetLaw.expect_comp_of_fiber_card_eq
    (history S h) (available S h) (fun f => f i) m hm
    (fun f hf => next_mem_available S h f i hi hf)
  intro x hx
  exact next_fiber_card_eq S h i x (h i) hx
    (next_mem_available S h h i hi (self_mem_history S h))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem card_available (S : Finset ι) (h : ι ↪ α) :
    (available S h).card = Fintype.card α - S.card := by
  simp [available, Finset.card_sdiff_of_subset (Finset.subset_univ (S.map h))]

theorem next_probability_given_history (S : Finset ι) (h : ι ↪ α) (i : ι)
    (hi : i ∉ S) (x : α) :
    (𝔼 f ∈ history S h, if f i = x then (1 : ℝ) else 0) =
      if x ∈ available S h then
        1 / ((Fintype.card α - S.card : ℕ) : ℝ) else 0 := by
  rw [expect_next_given_history S h i hi (fun y => if y = x then (1 : ℝ) else 0)]
  simp only [Finset.expect_eq_sum_div_card, card_available]
  split_ifs <;> simp_all

omit [DecidableEq ι] in

theorem range_fiber_card_eq (S T : Finset α) (hST : S.card = T.card) :
    ((Finset.univ.filter (fun f : ι ↪ α => Finset.univ.map f = S)).card) =
      ((Finset.univ.filter (fun f : ι ↪ α => Finset.univ.map f = T)).card) := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq S T hST
  apply Finset.card_equiv (postcompose τ)
  intro f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hf
    change Finset.univ.map (f.trans τ.toEmbedding) = T
    rw [← Finset.map_map, hf, hτ]
  · intro hf
    apply Finset.map_injective τ.toEmbedding
    rw [hτ]
    change Finset.univ.map (f.trans τ.toEmbedding) = T at hf
    simpa only [Finset.map_map] using hf

omit [DecidableEq ι] in

theorem expect_range (h : ι ↪ α) (g : Finset α → ℝ) :
    (𝔼 f : ι ↪ α, g (Finset.univ.map f)) =
      𝔼 S ∈ (Finset.univ : Finset α).powersetCard (Fintype.card ι), g S := by
  let R := Finset.univ.map h
  let m := ((Finset.univ : Finset (ι ↪ α)).filter
    (fun f => Finset.univ.map f = R)).card
  have hm : 0 < m := Finset.card_pos.mpr ⟨h, by simp [R]⟩
  apply PermutationSubsetLaw.expect_comp_of_fiber_card_eq
    Finset.univ ((Finset.univ : Finset α).powersetCard (Fintype.card ι))
    (fun f : ι ↪ α => Finset.univ.map f) m hm
  · intro f _
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp⟩
  · intro S hS
    apply range_fiber_card_eq S R
    simpa [R] using (Finset.mem_powersetCard.mp hS).2

def selfEmbeddingEquivPerm : (α ↪ α) ≃ Equiv.Perm α where
  toFun f := Equiv.ofBijective f ⟨f.injective, Finite.surjective_of_injective f.injective⟩
  invFun σ := σ.toEmbedding
  left_inv f := by ext x; rfl
  right_inv σ := by ext x; rfl

def permutationHistory (S : Finset α) (h : Equiv.Perm α) :
    Finset (Equiv.Perm α) :=
  Finset.univ.filter fun σ => ∀ j ∈ S, σ j = h j

theorem expect_permutation_next_given_history (S : Finset α) (h : Equiv.Perm α)
    (i : α) (hi : i ∉ S) (g : α → ℝ) :
    (𝔼 σ ∈ permutationHistory S h, g (σ i)) =
      𝔼 x ∈ available S h.toEmbedding, g x := by
  calc
    _ = 𝔼 f ∈ history S h.toEmbedding, g (f i) := by
      symm
      apply Finset.expect_equiv selfEmbeddingEquivPerm
      · intro f
        simp only [history, permutationHistory, Finset.mem_filter, Finset.mem_univ, true_and]
        rfl
      · intro f _
        rfl
    _ = _ := expect_next_given_history S h.toEmbedding i hi g

end
end Balanced.InjectionExposureLaw

end OAI
