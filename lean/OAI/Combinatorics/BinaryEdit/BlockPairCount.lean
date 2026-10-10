import Mathlib

namespace OAI

namespace TreeEdit.BinaryLower

/-- A componentwise chain in a rectangular integer grid has at most
`M + N - 1` points. This counts the block pairs visited by an increasing
subsequence matching; no alignment of block boundaries is assumed. -/
theorem card_grid_chain_le (s : Finset (ℕ × ℕ)) (M N : ℕ)
    (hbound : ∀ p ∈ s, p.1 < M ∧ p.2 < N)
    (hchain : ∀ p ∈ s, ∀ q ∈ s,
      (p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∨ (q.1 ≤ p.1 ∧ q.2 ≤ p.2)) :
    s.card ≤ M + N - 1 := by
  let rank : ℕ × ℕ → ℕ := fun p => p.1 + p.2
  have hinj : Set.InjOn rank s := by
    intro p hp q hq heq
    have h := hchain p hp q hq
    dsimp [rank] at heq
    rcases p with ⟨i, j⟩
    rcases q with ⟨i', j'⟩
    have hi : i = i' := by rcases h with h | h <;> omega
    have hj : j = j' := by rcases h with h | h <;> omega
    simp [hi, hj]
  have hsub : s.image rank ⊆ Finset.range (M + N - 1) := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    have hp' := hbound p hp
    simp only [Finset.mem_range]
    dsimp [rank]
    omega
  calc
    s.card = (s.image rank).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (M + N - 1)).card := Finset.card_le_card hsub
    _ = M + N - 1 := Finset.card_range _

/-- The distinct values attained by a componentwise monotone sequence of
block indices form a short grid chain. -/
theorem card_monotone_pair_image_le {r M N : ℕ}
    (f g : Fin r → ℕ) (hf : Monotone f) (hg : Monotone g)
    (hfb : ∀ a, f a < M) (hgb : ∀ a, g a < N) :
    (Finset.univ.image (fun a => (f a, g a))).card ≤ M + N - 1 := by
  apply card_grid_chain_le
  · intro p hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hfb a, hgb a⟩
  · intro p hp q hq
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
    rcases le_total a b with h | h
    · exact Or.inl ⟨hf h, hg h⟩
    · exact Or.inr ⟨hf h, hg h⟩

/-- The number of block pairs visited by an increasing bit matching between
words with `M` and `N` blocks of width `P` is at most `M + N - 1`. -/
theorem card_block_pair_image_le {r M N P : ℕ} (hP : 0 < P)
    (f g : Fin r → ℕ) (hf : Monotone f) (hg : Monotone g)
    (hfb : ∀ a, f a < M * P) (hgb : ∀ a, g a < N * P) :
    (Finset.univ.image (fun a => (f a / P, g a / P))).card ≤ M + N - 1 := by
  apply card_monotone_pair_image_le
  · intro a b hab
    exact Nat.div_le_div_right (hf hab)
  · intro a b hab
    exact Nat.div_le_div_right (hg hab)
  · intro a
    exact (Nat.div_lt_iff_lt_mul hP).mpr (hfb a)
  · intro a
    exact (Nat.div_lt_iff_lt_mul hP).mpr (hgb a)

/-- In the equal-length case, at most `2 * M - 1` block pairs occur. -/
theorem card_equal_block_pair_image_le {r M P : ℕ} (hP : 0 < P)
    (f g : Fin r → ℕ) (hf : Monotone f) (hg : Monotone g)
    (hfb : ∀ a, f a < M * P) (hgb : ∀ a, g a < M * P) :
    (Finset.univ.image (fun a => (f a / P, g a / P))).card ≤ 2 * M - 1 := by
  simpa [two_mul] using card_block_pair_image_le hP f g hf hg hfb hgb

/-- A fixed block pair occupies a consecutive portion of the matching.
This is the order-convexity fact needed for its minimal spans to contain
no positions matched under a different pair. -/
theorem monotone_pair_fiber_convex {ι : Type*} [Preorder ι]
    (f g : ι → ℕ) (hf : Monotone f) (hg : Monotone g)
    {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c)
    (h : (f a, g a) = (f c, g c)) : (f b, g b) = (f a, g a) := by
  have hfEq : f a = f c := congrArg Prod.fst h
  have hgEq : g a = g c := congrArg Prod.snd h
  have hfL := hf hab
  have hfR := hf hbc
  have hgL := hg hab
  have hgR := hg hbc
  apply Prod.ext <;> simp only <;> omega

end TreeEdit.BinaryLower

end OAI
