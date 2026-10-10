import OAI.Combinatorics.BinaryEdit.Model
import OAI.Combinatorics.TreeEdit.Alignments
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic

namespace OAI

noncomputable section
namespace TreeEdit.BinaryLower
namespace TaggedExtraction

universe u
variable {α : Type u}

/-- Every canonical LCS is witnessed by a numerically indexed increasing matching. -/
theorem exists_maximum_matching (x y : List α) :
    ∃ N : ℕ, N = lcs x y ∧ ∃ (u v : Fin N → ℕ)
      (hu : ∀ i, u i < x.length) (hv : ∀ i, v i < y.length),
      StrictMono u ∧ StrictMono v ∧
      (∀ i, x[u i]'(hu i) = y[v i]'(hv i)) := by
  obtain ⟨⟨f, g, hmatch⟩⟩ := exists_lcs_alignment x y
  refine ⟨lcs x y, rfl, (fun i => (f i).val), (fun i => (g i).val),
    (fun i => (f i).isLt), (fun i => (g i).isLt), f.strictMono, g.strictMono, ?_⟩
  intro i
  exact hmatch i

/-- A row obtained by concatenating equal-width blocks in increasing index order. -/
def blocks {m B : ℕ} (X : Fin m → Word α B) : List α :=
  (List.finRange m).flatMap fun i => (X i).val

lemma blocks_succ {m B : ℕ} (X : Fin (m + 1) → Word α B) :
    blocks X = (X 0).val ++ blocks (fun i => X i.succ) := by
  simp [blocks, List.finRange_succ, List.flatMap_map]

@[simp] lemma length_blocks {m B : ℕ} (X : Fin m → Word α B) :
    (blocks X).length = m * B := by
  induction m with
  | zero => simp [blocks]
  | succ m ih =>
    rw [blocks_succ]
    simp only [List.length_append, (X 0).property, ih]
    ring

lemma block_index_lt {m B : ℕ} (i : Fin m) (j : Fin B) :
    i.val * B + j.val < m * B := by
  calc
    i.val * B + j.val < i.val * B + B := Nat.add_lt_add_left j.isLt _
    _ = (i.val + 1) * B := by ring
    _ ≤ m * B := Nat.mul_le_mul_right B i.isLt

/-- Indexing a concatenated row at block `i` and within-block position `j`. -/
lemma getElem_blocks {m B : ℕ} (X : Fin m → Word α B) (i : Fin m) (j : Fin B) :
    (blocks X)[i.val * B + j.val]'(by rw [length_blocks]; exact block_index_lt i j) =
      (X i).val[j.val]'(by rw [(X i).property]; exact j.isLt) := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [blocks_succ, (X 0).property, j.isLt]
    · have hlo : B ≤ (i.val + 1) * B + j.val := by
        calc
          B ≤ (i.val + 1) * B := Nat.le_mul_of_pos_left B (Nat.succ_pos _)
          _ ≤ (i.val + 1) * B + j.val := Nat.le_add_right _ _
      have he : (i.val + 1) * B + j.val - B = i.val * B + j.val := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [Fin.val_succ, blocks_succ, List.getElem_append, (X 0).property,
        dite_eq_right (Nat.not_lt.mpr hlo), he] using ih (fun i => X i.succ) i

/-- `T` rows of `m` blocks of width `B`. -/
def rows {T m B : ℕ} (X : Fin T → Fin m → Word α B) : List α :=
  blocks fun a => ⟨blocks (X a), length_blocks (X a)⟩

lemma rows_eq_flatMap {T m B : ℕ} (X : Fin T → Fin m → Word α B) :
    rows X = (List.finRange T).flatMap
      (fun a => (List.finRange m).flatMap fun i => (X a i).val) := rfl

@[simp] lemma length_rows {T m B : ℕ} (X : Fin T → Fin m → Word α B) :
    (rows X).length = T * m * B := by
  simp only [rows, length_blocks]
  ring

lemma row_index_lt {T m B : ℕ} (a : Fin T) (i : Fin m) (j : Fin B) :
    a.val * (m * B) + (i.val * B + j.val) < T * m * B := by
  simpa only [Nat.mul_assoc] using
    block_index_lt a (⟨i.val * B + j.val, block_index_lt i j⟩ : Fin (m * B))

/-- Indexed extraction of a cell from the literal concatenation of rows. -/
lemma getElem_rows {T m B : ℕ} (X : Fin T → Fin m → Word α B)
    (a : Fin T) (i : Fin m) (j : Fin B) :
    (rows X)[a.val * (m * B) + (i.val * B + j.val)]'
      (by rw [length_rows]; exact row_index_lt a i j) =
      (X a i).val[j.val]'(by rw [(X a i).property]; exact j.isLt) := by
  have h := getElem_blocks
    (fun a => (⟨blocks (X a), length_blocks (X a)⟩ : Word α (m * B)))
    a (⟨i.val * B + j.val, block_index_lt i j⟩ : Fin (m * B))
  exact h.trans (getElem_blocks (X a) i j)

lemma row_quotient_lt {T m B p : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hp : p < T * m * B) : p / B / m < T := by
  rw [Nat.div_lt_iff_lt_mul hm]
  exact (Nat.div_lt_iff_lt_mul hB).2 hp

lemma row_quotient_decomposition (m B p : ℕ) :
    p / B / m * (m * B) + (p / B % m * B + p % B) = p := by
  calc
    p / B / m * (m * B) + (p / B % m * B + p % B) =
        (m * (p / B / m) + p / B % m) * B + p % B := by ring
    _ = p / B * B + p % B := by rw [Nat.div_add_mod]
    _ = p := by simpa only [Nat.mul_comm] using Nat.div_add_mod p B

/-- Quotient/remainder form matching the numerical tagged-row geometric lemmas. -/
lemma getElem_rows_quotient {T m B : ℕ} (X : Fin T → Fin m → Word α B)
    (hm : 0 < m) (hB : 0 < B) (p : ℕ) (hp : p < T * m * B) :
    (rows X)[p]'(by rw [length_rows]; exact hp) =
      (X ⟨p / B / m, row_quotient_lt hm hB hp⟩
         ⟨p / B % m, Nat.mod_lt _ hm⟩).val[p % B]'
        (by rw [(X _ _).property]; exact Nat.mod_lt _ hB) := by
  have h := getElem_rows X
    ⟨p / B / m, row_quotient_lt hm hB hp⟩
    ⟨p / B % m, Nat.mod_lt _ hm⟩ ⟨p % B, Nat.mod_lt _ hB⟩
  simpa only [row_quotient_decomposition] using h

/-- Pairwise-disjoint letter tags force equal matched positions to have the same block index.
The assumption is only cross-family disjointness; no row-boundary alignment is assumed. -/
lemma equal_symbols_same_tag {T m B : ℕ}
    (X Y : Fin T → Fin m → Word α B) (hm : 0 < m) (hB : 0 < B)
    (hdisjoint : ∀ (a b : Fin T) (i j : Fin m) (s : α),
      s ∈ (X a i).val → s ∈ (Y b j).val → i = j)
    (p q : ℕ) (hp : p < T * m * B) (hq : q < T * m * B)
    (heq : (rows X)[p]'(by rw [length_rows]; exact hp) =
      (rows Y)[q]'(by rw [length_rows]; exact hq)) :
    p / B % m = q / B % m := by
  rw [getElem_rows_quotient X hm hB p hp,
      getElem_rows_quotient Y hm hB q hq] at heq
  have hleft := List.getElem_mem
    (l := (X ⟨p / B / m, row_quotient_lt hm hB hp⟩
      ⟨p / B % m, Nat.mod_lt _ hm⟩).val)
    (n := p % B) (by rw [(X _ _).property]; exact Nat.mod_lt _ hB)
  have hright := List.getElem_mem
    (l := (Y ⟨q / B / m, row_quotient_lt hm hB hq⟩
      ⟨q / B % m, Nat.mod_lt _ hm⟩).val)
    (n := q % B) (by rw [(Y _ _).property]; exact Nat.mod_lt _ hB)
  rw [← heq] at hright
  exact congrArg Fin.val (hdisjoint _ _ _ _ _ hleft hright)

/-- A longest matching of tagged rows supplies the precise natural-coordinate interface
used by the split-row gap bound, including the zero-match case. -/
theorem exists_maximum_row_matching {T m B : ℕ}
    (X Y : Fin T → Fin m → Word α B) (hm : 0 < m) (hB : 0 < B)
    (hdisjoint : ∀ (a b : Fin T) (i j : Fin m) (s : α),
      s ∈ (X a i).val → s ∈ (Y b j).val → i = j) :
    ∃ N : ℕ, N = lcs (rows X) (rows Y) ∧
      ∃ (u v : Fin N → ℕ) (hu : ∀ i, u i < T * m * B)
        (hv : ∀ i, v i < T * m * B),
        StrictMono u ∧ StrictMono v ∧
        (∀ i, u i / B % m = v i / B % m) ∧
        (∀ i, (rows X)[u i]'(by rw [length_rows]; exact hu i) =
          (rows Y)[v i]'(by rw [length_rows]; exact hv i)) := by
  obtain ⟨N, hN, u, v, hu, hv, hsu, hsv, heq⟩ :=
    exists_maximum_matching (rows X) (rows Y)
  have hu' : ∀ i, u i < T * m * B := by simpa only [length_rows] using hu
  have hv' : ∀ i, v i < T * m * B := by simpa only [length_rows] using hv
  refine ⟨N, hN, u, v, hu', hv', hsu, hsv, ?_, heq⟩
  intro i
  exact equal_symbols_same_tag X Y hm hB hdisjoint (u i) (v i) (hu' i) (hv' i) (heq i)

/-- Ordered tags expressed as a single decoder imply the disjointness premise above. -/
lemma cross_disjoint_of_tags {T m B : ℕ}
    (X Y : Fin T → Fin m → Word α B) (tag : α → Fin m)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i) :
    ∀ (a b : Fin T) (i j : Fin m) (s : α),
      s ∈ (X a i).val → s ∈ (Y b j).val → i = j := by
  intro a b i j s hx hy
  exact (hX a i s hx).symm.trans (hY b j s hy)

/-- The global-symbol interface required by the tagged slice-alignment theorem. -/
lemma equal_symbols_same_tag_of_decoder {T m B : ℕ}
    (X Y : Fin T → Fin m → Word α B) (tag : α → Fin m)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i)
    (hm : 0 < m) (hB : 0 < B)
    (p q : ℕ) (hp : p < T * m * B) (hq : q < T * m * B)
    (heq : (rows X)[p]'(by rw [length_rows]; exact hp) =
      (rows Y)[q]'(by rw [length_rows]; exact hq)) :
    p / B % m = q / B % m :=
  equal_symbols_same_tag X Y hm hB (cross_disjoint_of_tags X Y tag hX hY) p q hp hq heq

end TaggedExtraction
end TreeEdit.BinaryLower

end

end OAI
