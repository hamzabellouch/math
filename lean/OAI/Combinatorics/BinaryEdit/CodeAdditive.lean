import OAI.Combinatorics.BinaryEdit.CodeEqualMatches
import OAI.Combinatorics.BinaryEdit.CodeNumerics
import OAI.Combinatorics.BinaryEdit.EncodingUpper
import OAI.Combinatorics.BinaryEdit.LCS

namespace OAI

/-! The longest encoded matching is partitioned by equality of its
original block labels. Segment separation and the span loss budget bound
the number of unequal-label matches. -/

namespace TreeEdit.BinaryLower.Code

universe u v

/-- The original letter whose block contains a specified encoded position. -/
def originalLetterAtBit {α : Type u} {M P : ℕ} (x : List α)
    (hx : x.length = M) (hP : 0 < P) (q : Fin (M*P)) : α :=
  x.get ⟨q.val/P, by rw [hx]; exact (Nat.div_lt_iff_lt_mul hP).mpr q.isLt⟩

/-- A bit of the actual concatenation, with its prescribed-length indexing. -/
def encodedBit {α : Type u} {β : Type v} {M P : ℕ}
    (c : α → Word β P) (x : List α) (hx : x.length = M)
    (q : Fin (M*P)) : β :=
  (encode c x).get ⟨q.val, by rw [length_encode, hx]; exact q.isLt⟩

/-- Reading all encoded positions reconstructs the concrete concatenation. -/
@[simp] theorem ofFn_encodedBit {α : Type u} {β : Type v} {M P : ℕ}
    (c : α → Word β P) (x : List α) (hx : x.length = M) :
    List.ofFn (encodedBit c x hx) = encode c x := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, length_encode, hx]
  · intro i hi hi'
    simp only [List.getElem_ofFn, encodedBit, List.get_eq_getElem]

/-- Optional lookup at an encoded position's block always succeeds and
returns exactly its original letter. This avoids partial-label conventions. -/
theorem getElem?_blockLetter {α : Type u} {M P : ℕ} (x : List α)
    (hx : x.length = M) (hP : 0 < P) (q : Fin (M*P)) :
    x[q.val/P]? = some (originalLetterAtBit x hx hP q) := by
  have hq : q.val/P < x.length := by
    rw [hx]
    exact (Nat.div_lt_iff_lt_mul hP).mpr q.isLt
  simp only [List.getElem?_eq_getElem hq, originalLetterAtBit, List.get_eq_getElem]

/-- Precisely the selected unequal-original-label edges of a matching. -/
noncomputable def unequalEdges {α : Type u} {M P r : ℕ}
    (x y : List α) (hx : x.length = M) (hy : y.length = M) (hP : 0 < P)
    (f g : Fin r → Fin (M*P)) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun t =>
    originalLetterAtBit x hx hP (f t) ≠ originalLetterAtBit y hy hP (g t))

/-- Unequal-edge selection can equivalently be expressed by a total predicate
on the two natural-number block indices using optional original-word lookup. -/
theorem unequalEdges_eq_filter_getElem? {α : Type u} [DecidableEq α] {M P r : ℕ}
    (x y : List α) (hx : x.length = M) (hy : y.length = M) (hP : 0 < P)
    (f g : Fin r → Fin (M*P)) :
    unequalEdges x y hx hy hP f g =
      Finset.univ.filter (fun t => x[(f t).val/P]? ≠ y[(g t).val/P]?) := by
  classical
  ext t
  simp only [unequalEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    getElem?_blockLetter x hx hP, getElem?_blockLetter y hy hP, ne_eq, Option.some.injEq]

/-- Equal-label coloring and the unequal-label estimate, for actual encoded
words and a matching of their longest-common-subsequence length. -/
theorem additive_of_longest_unequal_bound {α : Type u} {β : Type v}
    {M P a₀ : ℕ} (c : α → Word β P) (x y : List α)
    (hx : x.length = M) (hy : y.length = M) (hP : 0 < P)
    (f g : Fin (lcs (encode c x) (encode c y)) → Fin (M*P))
    (hf : StrictMono f) (hg : StrictMono g)
    (hunequal : (unequalEdges x y hx hy hP f g).card ≤
      200*(M*P-lcs (encode c x) (encode c y))+2*M*a₀) :
    P*deficit M x y ≤ 201*deficit (M*P) (encode c x) (encode c y)+2*M*a₀ := by
  classical
  let r := lcs (encode c x) (encode c y)
  let eqedges : Finset (Fin r) := Finset.univ.filter fun t =>
    originalLetterAtBit x hx hP (f t) = originalLetterAtBit y hy hP (g t)
  have hfx : ∀ t, (f t).val/P < x.length := by
    intro t
    rw [hx]
    exact (Nat.div_lt_iff_lt_mul hP).mpr (f t).isLt
  have hgy : ∀ t, (g t).val/P < y.length := by
    intro t
    rw [hy]
    exact (Nat.div_lt_iff_lt_mul hP).mpr (g t).isLt
  have hequal : eqedges.card ≤ P*lcs x y := by
    apply equal_label_subset_card_le hP x y (fun t => (f t).val) (fun t => (g t).val)
      (Fin.val_strictMono.comp hf) (Fin.val_strictMono.comp hg) hfx hgy eqedges
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  have hpartition : r = eqedges.card + (unequalEdges x y hx hy hP f g).card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin r)))
      (p := fun t => originalLetterAtBit x hx hP (f t) =
        originalLetterAtBit y hy hP (g t))
    simpa only [eqedges, unequalEdges, Finset.card_univ, Fintype.card_fin] using h.symm
  have hr : r ≤ M*P := by
    have h := lcs_le_length_left (encode c x) (encode c y)
    simpa only [length_encode, hx] using h
  have hL : lcs x y ≤ M := by simpa only [hx] using lcs_le_length_left x y
  exact block_counts_to_additive hpartition
    (show r+deficit (M*P) (encode c x) (encode c y) = M*P by
      simp only [deficit]; exact Nat.add_sub_of_le hr)
    (show deficit M x y+lcs x y=M by
      simp only [deficit]; exact Nat.sub_add_cancel hL)
    hequal hunequal

/-- An unequal count proved for every actual encoded matching yields the
source additive estimate by choosing a longest encoded matching. -/
theorem additive_of_unequal_matching_bound {α : Type u} {β : Type v}
    {M P a₀ : ℕ} (c : α → Word β P) (x y : List α)
    (hx : x.length = M) (hy : y.length = M) (hP : 0 < P)
    (hunequal : ∀ (r : ℕ) (f g : Fin r → Fin (M*P)),
      StrictMono f → StrictMono g →
      (∀ t, encodedBit c x hx (f t) = encodedBit c y hy (g t)) →
      (unequalEdges x y hx hy hP f g).card ≤ 200*(M*P-r)+2*M*a₀) :
    P*deficit M x y ≤ 201*deficit (M*P) (encode c x) (encode c y)+2*M*a₀ := by
  have hencx : (encode c x).length = M*P := by rw [length_encode, hx]
  have hency : (encode c y).length = M*P := by rw [length_encode, hy]
  obtain ⟨⟨f₀, g₀, hmatch⟩⟩ := exists_lcs_alignment (encode c x) (encode c y)
  let f := fun t => Fin.cast hencx (f₀ t)
  let g := fun t => Fin.cast hency (g₀ t)
  have hf : StrictMono f := (Fin.cast_strictMono hencx).comp f₀.strictMono
  have hg : StrictMono g := (Fin.cast_strictMono hency).comp g₀.strictMono
  apply additive_of_longest_unequal_bound c x y hx hy hP f g hf hg
  apply hunequal _ f g hf hg
  intro t
  simpa only [encodedBit, f, g, Fin.cast] using hmatch t

end TreeEdit.BinaryLower.Code

end OAI
