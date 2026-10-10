import OAI.Combinatorics.LowSpaceSubsetSum.Counting.MatchPotential

namespace OAI

/-!
# Linear exact-key search for the separator's terminal arrays

At a terminal separator node every left/right pair is disjoint. One equal
weight key therefore suffices. This loop stops at the first equal key and
never enumerates its Cartesian tie group. The finite reader law supplies
exactness, and the ledger charges at most two reads per control step.
-/

namespace LowSpaceSubsetSum
namespace SortedFind

variable {α β σ₁ σ₂ : Type*}

def runAcc (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) :
    ℕ → σ₁ → σ₂ → ℕ → Bool × ℕ
  | 0, _, _, queries => (false, queries)
  | fuel + 1, s₁, s₂, queries =>
    match read₁ s₁ with
    | none => (false, queries + 1)
    | some (x, s₁') => match read₂ s₂ with
      | none => (false, queries + 2)
      | some (y, s₂') =>
        if key₁ x < key₂ y then runAcc read₁ key₁ read₂ key₂ fuel s₁' s₂ (queries + 2)
        else if key₂ y < key₁ x then runAcc read₁ key₁ read₂ key₂ fuel s₁ s₂' (queries + 2)
        else (true, queries + 2)

theorem queries_le (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (fuel : ℕ) (s₁ : σ₁) (s₂ : σ₂) (queries : ℕ) :
    (runAcc read₁ key₁ read₂ key₂ fuel s₁ s₂ queries).2 ≤ queries + 2 * fuel := by
  induction fuel generalizing s₁ s₂ queries with
  | zero => simp [runAcc]
  | succ fuel ih =>
    unfold runAcc
    split
    · dsimp
      omega
    · split
      · dsimp
        omega
      · split
        · exact (ih _ _ _).trans (by omega)
        · split
          · exact (ih _ _ _).trans (by omega)
          · dsimp
            omega

theorem sound (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (fuel : ℕ) (s₁ : σ₁) (s₂ : σ₂) (queries : ℕ)
    (hyes : (runAcc read₁ key₁ read₂ key₂ fuel s₁ s₂ queries).1 = true) :
    ∃ x ∈ view₁ s₁, ∃ y ∈ view₂ s₂, key₁ x = key₂ y := by
  induction fuel generalizing s₁ s₂ queries with
  | zero => simp [runAcc] at hyes
  | succ fuel ih =>
    have h₁ := hread₁ s₁
    have h₂ := hread₂ s₂
    cases hx : read₁ s₁ with
    | none => simp [runAcc, hx] at hyes
    | some xp =>
      obtain ⟨x, s₁'⟩ := xp
      simp only [hx] at h₁
      cases hy : read₂ s₂ with
      | none => simp [runAcc, hx, hy] at hyes
      | some yp =>
        obtain ⟨y, s₂'⟩ := yp
        simp only [hy] at h₂
        by_cases hlt : key₁ x < key₂ y
        · simp only [runAcc, hx, hy, hlt, ↓reduceIte] at hyes
          obtain ⟨a, ha, b, hb, heq⟩ := ih _ _ _ hyes
          exact ⟨a, by rw [h₁]; exact List.mem_cons_of_mem _ ha, b, hb, heq⟩
        · by_cases hgt : key₂ y < key₁ x
          · simp only [runAcc, hx, hy, hlt, hgt, ↓reduceIte] at hyes
            obtain ⟨a, ha, b, hb, heq⟩ := ih _ _ _ hyes
            exact ⟨a, ha, b, by rw [h₂]; exact List.mem_cons_of_mem _ hb, heq⟩
          · exact ⟨x, by rw [h₁]; simp, y, by rw [h₂]; simp, by omega⟩

theorem correct (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (fuel : ℕ) (s₁ : σ₁) (s₂ : σ₂) (queries : ℕ)
    (hs₁ : (view₁ s₁).Pairwise (fun x y => key₁ x ≤ key₁ y))
    (hs₂ : (view₂ s₂).Pairwise (fun x y => key₂ x ≤ key₂ y))
    (hfuel : (view₁ s₁).length + (view₂ s₂).length < fuel) :
    (runAcc read₁ key₁ read₂ key₂ fuel s₁ s₂ queries).1 = true ↔
      0 < MatchPotential.count key₁ key₂ (view₁ s₁) (view₂ s₂) := by
  induction fuel generalizing s₁ s₂ queries with
  | zero => omega
  | succ fuel ih =>
    have h₁ := hread₁ s₁
    have h₂ := hread₂ s₂
    cases hx : read₁ s₁ with
    | none =>
      simp only [hx] at h₁
      simp [runAcc, hx, h₁, MatchPotential.count]
    | some xp =>
      obtain ⟨x, s₁'⟩ := xp
      simp only [hx] at h₁
      cases hy : read₂ s₂ with
      | none =>
        simp only [hy] at h₂
        have hz := MatchPotential.eq_zero key₁ key₂ (view₁ s₁) [] (by simp)
        simp [runAcc, hx, hy, h₂, hz]
      | some yp =>
        obtain ⟨y, s₂'⟩ := yp
        simp only [hy] at h₂
        have hs₁' := (List.pairwise_cons.mp (h₁ ▸ hs₁)).2
        have hs₂' := (List.pairwise_cons.mp (h₂ ▸ hs₂)).2
        by_cases hlt : key₁ x < key₂ y
        · have hskip := MatchPotential.skip_left key₁ key₂ x (view₁ s₁') (view₂ s₂) (by
            intro z hz
            rw [h₂] at hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hlt
            · exact hlt.trans_le ((List.pairwise_cons.mp (h₂ ▸ hs₂)).1 z hz))
          rw [← h₁] at hskip
          simp only [runAcc, hx, hy, hlt, ↓reduceIte, hskip]
          exact ih s₁' s₂ _ hs₁' hs₂ (by rw [h₁] at hfuel; simp only [List.length_cons] at hfuel; omega)
        · by_cases hgt : key₂ y < key₁ x
          · have hskip := MatchPotential.skip_right key₁ key₂ (view₁ s₁) y (view₂ s₂') (by
              intro z hz
              rw [h₁] at hz
              rcases List.mem_cons.mp hz with rfl | hz
              · exact hgt
              · exact hgt.trans_le ((List.pairwise_cons.mp (h₁ ▸ hs₁)).1 z hz))
            rw [← h₂] at hskip
            simp only [runAcc, hx, hy, hlt, hgt, ↓reduceIte, hskip]
            exact ih s₁ s₂' _ hs₁ hs₂' (by rw [h₂] at hfuel; simp only [List.length_cons] at hfuel; omega)
          · have heq : key₁ x = key₂ y := by omega
            have hpos := (MatchPotential.positive_iff key₁ key₂ (view₁ s₁) (view₂ s₂)).mpr
              ⟨x, by rw [h₁]; simp, y, by rw [h₂]; simp, heq⟩
            simp [runAcc, hx, hy, hlt, hgt, hpos]

end SortedFind
end LowSpaceSubsetSum

end OAI
