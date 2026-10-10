import OAI.Combinatorics.MatrixRemoval.Model

namespace OAI

/-!
The anchor/body extension step for arbitrary repairs.
The finite-order gluing lemma is independent of the host construction.
-/

universe uAlpha

noncomputable section

namespace Problem348

/-- Append two values to a function on a finite initial segment. -/
def appendTwo {α : Type uAlpha} {k : ℕ} (f : Fin k → α) (a b : α) :
    Fin (k + 2) → α := fun i =>
  if hi : i.val < k then f ⟨i.val, hi⟩ else if i.val = k then a else b

@[simp] theorem appendTwo_initial {α : Type uAlpha} {k : ℕ}
    (f : Fin k → α) (a b : α) (i : Fin k) :
    appendTwo f a b ⟨i.val, by omega⟩ = f i := by
  simp [appendTwo, i.isLt]

@[simp] theorem appendTwo_first {α : Type uAlpha} {k : ℕ}
    (f : Fin k → α) (a b : α) :
    appendTwo f a b ⟨k, by omega⟩ = a := by
  simp [appendTwo]

@[simp] theorem appendTwo_second {α : Type uAlpha} {k : ℕ}
    (f : Fin k → α) (a b : α) :
    appendTwo f a b ⟨k + 1, by omega⟩ = b := by
  simp [appendTwo]

theorem strictMono_appendTwo {α : Type uAlpha} [Preorder α] {k : ℕ}
    (f : Fin k → α) (a b : α) (hf : StrictMono f)
    (ha : ∀ i, f i < a) (hab : a < b) :
    StrictMono (appendTwo f a b) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simpa [appendTwo, hi, hj] using
        hf (show (⟨i.val, hi⟩ : Fin k) < ⟨j.val, hj⟩ from hij')
    · by_cases hjk : j.val = k
      · simpa [appendTwo, hi, hj, hjk] using ha ⟨i.val, hi⟩
      · simpa [appendTwo, hi, hj, hjk] using lt_trans (ha ⟨i.val, hi⟩) hab
  · have hik : i.val = k := by omega
    have hjk : j.val = k + 1 := by omega
    simpa [appendTwo, hik, hjk] using hab

/-- The increasing map obtained by appending two positions after an anchor. -/
def appendTwoIncreasing {k n : ℕ} (r : IncreasingMap k n)
    (a b : Fin n) (ha : ∀ i, r.val i < a) (hab : a < b) :
    IncreasingMap (k + 2) n :=
  ⟨appendTwo r.val a b, strictMono_appendTwo r.val a b r.property ha hab⟩

/-- An anchor and the four body entries reproduce every entry of the fixed pattern. -/
theorem appendTwo_matches_fixedH {n : ℕ} (B : BinaryMatrix n)
    (r c : IncreasingMap 64 n) (r₀ r₁ c₀ c₁ : Fin n)
    (hanchor : ∀ u v, B (r.val u) (c.val v) = anchor64 u v)
    (hrow₀ : ∀ v, B r₀ (c.val v) = decide (v.val = 0))
    (hrow₁ : ∀ v, B r₁ (c.val v) = decide (v.val = 1))
    (hcol₀ : ∀ u, B (r.val u) c₀ = decide (u.val = 0))
    (hcol₁ : ∀ u, B (r.val u) c₁ = decide (u.val = 1))
    (h₀₀ : B r₀ c₀ = true) (h₀₁ : B r₀ c₁ = false)
    (h₁₀ : B r₁ c₀ = true) (h₁₁ : B r₁ c₁ = true) :
    ∀ i j : Fin 66,
      B (appendTwo r.val r₀ r₁ i) (appendTwo c.val c₀ c₁ j) = fixedH i j := by
  intro i j
  by_cases hi : i.val < 64
  · by_cases hj : j.val < 64
    · simpa [appendTwo, fixedH, hi, hj] using
        hanchor ⟨i.val, hi⟩ ⟨j.val, hj⟩
    · have hjcases : j.val = 64 ∨ j.val = 65 := by omega
      rcases hjcases with hj₀ | hj₁
      · simpa [appendTwo, fixedH, hi, hj, hj₀] using hcol₀ ⟨i.val, hi⟩
      · simpa [appendTwo, fixedH, hi, hj, hj₁] using hcol₁ ⟨i.val, hi⟩
  · have hicases : i.val = 64 ∨ i.val = 65 := by omega
    by_cases hj : j.val < 64
    · rcases hicases with hi₀ | hi₁
      · simpa [appendTwo, fixedH, hi, hj, hi₀] using hrow₀ ⟨j.val, hj⟩
      · simpa [appendTwo, fixedH, hi, hj, hi₁] using hrow₁ ⟨j.val, hj⟩
    · have hjcases : j.val = 64 ∨ j.val = 65 := by omega
      rcases hicases with hi₀ | hi₁ <;> rcases hjcases with hj₀ | hj₁ <;>
        simp [appendTwo, fixedH, *]

/-- The exact anchor-extension bridge needed by arbitrary-repair propagation. -/
theorem not_HFree_of_anchor_body {n : ℕ} (B : BinaryMatrix n)
    (r c : IncreasingMap 64 n) (r₀ r₁ c₀ c₁ : Fin n)
    (hr : ∀ i, r.val i < r₀) (hr₀₁ : r₀ < r₁)
    (hc : ∀ j, c.val j < c₀) (hc₀₁ : c₀ < c₁)
    (hanchor : ∀ u v, B (r.val u) (c.val v) = anchor64 u v)
    (hrow₀ : ∀ v, B r₀ (c.val v) = decide (v.val = 0))
    (hrow₁ : ∀ v, B r₁ (c.val v) = decide (v.val = 1))
    (hcol₀ : ∀ u, B (r.val u) c₀ = decide (u.val = 0))
    (hcol₁ : ∀ u, B (r.val u) c₁ = decide (u.val = 1))
    (h₀₀ : B r₀ c₀ = true) (h₀₁ : B r₀ c₁ = false)
    (h₁₀ : B r₁ c₀ = true) (h₁₁ : B r₁ c₁ = true) :
    ¬ HFree fixedH B := by
  classical
  let rr := appendTwoIncreasing r r₀ r₁ hr hr₀₁
  let cc := appendTwoIncreasing c c₀ c₁ hc hc₀₁
  have hmem : (rr, cc) ∈ orderedCopies fixedH B := by
    simp only [orderedCopies, Finset.mem_filter, Finset.mem_univ, true_and]
    exact appendTwo_matches_fixedH B r c r₀ r₁ c₀ c₁ hanchor hrow₀ hrow₁
      hcol₀ hcol₁ h₀₀ h₀₁ h₁₀ h₁₁
  have hpos : 0 < copyCount fixedH B :=
    Finset.card_pos.mpr ⟨(rr, cc), hmem⟩
  exact Nat.ne_of_gt hpos

end Problem348

end

end OAI
