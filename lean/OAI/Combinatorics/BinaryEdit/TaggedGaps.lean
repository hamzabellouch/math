import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace OAI

/-! Gap accounting for split rows in ordered-tag alignments. -/

namespace TreeEdit.BinaryLower.Tagged

open Finset

/-- The sum of the open gaps of an increasing matching telescopes. -/
theorem sum_open_gaps {n : ℕ} (v : Fin (n + 1) → ℕ) :
    (∑ i : Fin n, ((v i.succ : ℝ) - (v i.castSucc : ℝ) - 1)) =
      (v (Fin.last n) : ℝ) - (v 0 : ℝ) - n := by
  have hs := Fin.sum_univ_succ (fun i : Fin (n + 1) => (v i : ℝ))
  have ht := Fin.sum_univ_castSucc (fun i : Fin (n + 1) => (v i : ℝ))
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  linarith

/-- Chosen disjoint gaps cannot exceed the total number of unmatched target
positions. No assumption about aligned row boundaries is made. -/
theorem selected_gap_bound {n N : ℕ} (v : Fin (n + 1) → ℕ)
    (hv : StrictMono v) (hN : ∀ i, v i < N) (S : Finset (Fin n))
    (g : ℝ) (hg : ∀ i ∈ S, g ≤ (v i.succ : ℝ) - (v i.castSucc : ℝ) - 1) :
    (S.card : ℝ) * g ≤ (N : ℝ) - (n + 1) := by
  have hpos (i : Fin n) : 0 ≤ (v i.succ : ℝ) - (v i.castSucc : ℝ) - 1 := by
    have h := hv (show i.castSucc < i.succ by simp)
    have hc : (v i.castSucc : ℝ) + 1 ≤ (v i.succ : ℝ) := by exact_mod_cast h
    linarith
  have hsum : (S.card : ℝ) * g ≤
      ∑ i : Fin n, ((v i.succ : ℝ) - (v i.castSucc : ℝ) - 1) := by
    calc
      (S.card : ℝ) * g = ∑ i ∈ S, g := by simp
      _ ≤ ∑ i ∈ S, ((v i.succ : ℝ) - (v i.castSucc : ℝ) - 1) :=
        sum_le_sum hg
      _ ≤ ∑ i : Fin n, ((v i.succ : ℝ) - (v i.castSucc : ℝ) - 1) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ S) (by intro i _ _; exact hpos i)
  rw [sum_open_gaps] at hsum
  have hlast : (v (Fin.last n) : ℝ) + 1 ≤ (N : ℝ) := by
    exact_mod_cast hN (Fin.last n)
  have hzero : 0 ≤ (v 0 : ℝ) := Nat.cast_nonneg _
  linarith

/-- Equal row indices force the ordered tags of two source positions to be
nondecreasing. -/
theorem tag_le_of_same_row {a b m B : ℕ} (hab : a ≤ b)
    (hrow : a / B / m = b / B / m) :
    (a / B) % m ≤ (b / B) % m := by
  have hab' : a / B ≤ b / B := Nat.div_le_div_right hab
  have ha := Nat.mod_add_div (a / B) m
  have hb := Nat.mod_add_div (b / B) m
  rw [hrow] at ha
  omega

/-- A transition to a later target row, while staying in one source row,
forces at least `(m-1)*B` skipped target positions. -/
theorem tagged_gap {a b c d m B : ℕ} (hm : 1 ≤ m) (hB : 0 < B)
    (hab : a ≤ b) (hsource : a / B / m = b / B / m)
    (htarget : c / B / m < d / B / m)
    (htag₀ : (a / B) % m = (c / B) % m)
    (htag₁ : (b / B) % m = (d / B) % m) :
    c + 1 + (m - 1) * B ≤ d := by
  have htag : (c / B) % m ≤ (d / B) % m := by
    rw [← htag₀, ← htag₁]
    exact tag_le_of_same_row hab hsource
  have hc := Nat.mod_add_div (c / B) m
  have hd := Nat.mod_add_div (d / B) m
  have hmrow := Nat.mul_le_mul_left m (Nat.succ_le_of_lt htarget)
  have hblocks : c / B + m ≤ d / B := by nlinarith
  have hmul := Nat.mul_le_mul_left B hblocks
  have hc' := Nat.mod_add_div c B
  have hd' := Nat.mod_add_div d B
  have hrem := Nat.mod_lt c hB
  have hpred : m - 1 + 1 = m := by omega
  have heq := congrArg (fun t : ℕ => t * B) hpred
  calc
    c + 1 + (m - 1) * B = (c % B + 1) + B * (c / B) + (m - 1) * B := by omega
    _ ≤ B + B * (c / B) + (m - 1) * B := by omega
    _ = B * (c / B + m) := by nlinarith [heq]
    _ ≤ B * (d / B) := hmul
    _ ≤ d := by omega

/-- Consecutive matching entries that cross a target-row boundary without
crossing a source-row boundary. -/
def splitTransitions {n : ℕ} (m B : ℕ) (u v : Fin (n + 1) → ℕ) :
    Finset (Fin n) :=
  univ.filter fun i => u i.castSucc / B / m = u i.succ / B / m ∧
    v i.castSucc / B / m ≠ v i.succ / B / m

/-- Source rows which contain such a transition. -/
def splitRows {n : ℕ} (m B : ℕ) (u v : Fin (n + 1) → ℕ) : Finset ℕ :=
  (splitTransitions m B u v).image fun i => u i.castSucc / B / m

/-- For a monotone row map, equality on adjoining entries in a row implies
equality throughout that row's matching fiber. -/
theorem constant_on_row_fiber {n : ℕ} (R S : Fin (n + 1) → ℕ)
    (hR : Monotone R) (r : ℕ)
    (hstep : ∀ i : Fin n, R i.castSucc = r → R i.succ = r →
      S i.castSucc = S i.succ) :
    ∀ i j, R i = r → R j = r → S i = S j := by
  have hordered : ∀ j : Fin (n + 1), ∀ i, i ≤ j → R i = r → R j = r →
      S i = S j := by
    intro j
    induction j using Fin.induction with
    | zero =>
        intro i hi _ _
        have : i = 0 := le_antisymm hi (Fin.zero_le i)
        subst i
        rfl
    | succ j ih =>
        intro i hij hir hjr
        by_cases heq : i = j.succ
        · subst i; rfl
        have hip : i ≤ j.castSucc := by
          apply Fin.le_iff_val_le_val.2
          have hh := Fin.le_iff_val_le_val.1 hij
          have hn : i.val ≠ j.succ.val := by
            intro h
            exact heq (Fin.ext h)
          simp only [Fin.val_succ, Fin.val_castSucc] at *
          omega
        have hpr : R j.castSucc = r := by
          have hlo := hR hip
          have hhi := hR (show j.castSucc ≤ j.succ by exact Fin.le_iff_val_le_val.2 (Nat.le_succ _))
          omega
        exact (ih i hip hir hpr).trans (hstep j hpr hjr)
  intro i j hi hj
  rcases le_total i j with hij | hji
  · exact hordered j i hij hi hj
  · exact (hordered i j hji hj hi).symm

/-- A row not counted as split sends all its matches to one target row. -/
theorem target_row_eq_of_not_split {n m B r : ℕ}
    (u v : Fin (n + 1) → ℕ) (hu : Monotone u)
    (hr : r ∉ splitRows m B u v) :
    ∀ i j, u i / B / m = r → u j / B / m = r →
      v i / B / m = v j / B / m := by
  apply constant_on_row_fiber (fun i => u i / B / m) (fun i => v i / B / m)
  · intro i j hij
    exact Nat.div_le_div_right (Nat.div_le_div_right (hu hij))
  · intro i hi hj
    by_contra hne
    apply hr
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi.trans hj.symm, hne⟩, hi⟩

/-- The transition definition counts exactly the rows with matches in two
distinct target rows. -/
theorem mem_splitRows_iff {n m B r : ℕ}
    (u v : Fin (n + 1) → ℕ) (hu : Monotone u) :
    r ∈ splitRows m B u v ↔
      ∃ i j, u i / B / m = r ∧ u j / B / m = r ∧
        v i / B / m ≠ v j / B / m := by
  constructor
  · intro hr
    obtain ⟨i, hi, hir⟩ := mem_image.mp hr
    have ht := (mem_filter.mp hi).2
    exact ⟨i.castSucc, i.succ, hir, ht.1.symm.trans hir, ht.2⟩
  · rintro ⟨i, j, hi, hj, hne⟩
    by_contra hr
    exact hne (target_row_eq_of_not_split u v hu hr i j hi hj)

/-- Row indices of positions in a `T`-row word are strictly below `T`. -/
theorem row_index_lt {p T m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hp : p < T * m * B) : p / B / m < T := by
  apply (Nat.div_lt_iff_lt_mul hm).2
  apply (Nat.div_lt_iff_lt_mul hB).2
  exact hp

theorem splitRows_subset_range {n T m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (u v : Fin (n + 1) → ℕ) (hu : ∀ i, u i < T * m * B) :
    splitRows m B u v ⊆ range T := by
  intro r hr
  obtain ⟨i, _, rfl⟩ := mem_image.mp hr
  exact mem_range.mpr (row_index_lt hm hB (hu i.castSucc))

/-- Passing a set of valid natural row indices to `Fin T` preserves its
cardinality. -/
theorem card_fin_rows {T : ℕ} (S : Finset ℕ) (hS : S ⊆ range T) :
    (univ.filter fun r : Fin T => r.val ∈ S).card = S.card := by
  classical
  apply card_bij (fun r _ => r.val)
  · intro r hr
    exact (mem_filter.mp hr).2
  · intro r _ s _ hrs
    exact Fin.ext hrs
  · intro r hr
    refine ⟨⟨r, mem_range.mp (hS hr)⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    exact hr

/-- Per-row-pair matching bounds apply to every nonsplit source row. Empty
source fibers are included rather than discarded. -/
theorem nonsplit_row_card_le {n T m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (u v : Fin (n + 1) → ℕ) (hu : Monotone u)
    (hv : ∀ i, v i < T * m * B) (d : ℝ) (hd : d ≤ (m * B : ℕ))
    (hlocal : ∀ a < T, ∀ b < T,
      ((univ.filter fun i : Fin (n + 1) =>
        u i / B / m = a ∧ v i / B / m = b).card : ℝ) ≤ (m * B : ℕ) - d)
    {a : ℕ} (ha : a < T) (haS : a ∉ splitRows m B u v) :
    ((univ.filter fun i : Fin (n + 1) => u i / B / m = a).card : ℝ) ≤
      (m * B : ℕ) - d := by
  classical
  let S := univ.filter fun i : Fin (n + 1) => u i / B / m = a
  change (S.card : ℝ) ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨t, ht⟩ := hS
    have hta : u t / B / m = a := (mem_filter.mp ht).2
    have heq : S = univ.filter fun i : Fin (n + 1) =>
        u i / B / m = a ∧ v i / B / m = v t / B / m := by
      ext i
      simp only [S, mem_filter, mem_univ, true_and]
      constructor
      · intro hi
        exact ⟨hi, target_row_eq_of_not_split u v hu haS i t hi hta⟩
      · exact And.left
    rw [heq]
    exact hlocal a ha _ (row_index_lt hm hB (hv t))
  · have hzero : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    rw [hzero]
    simp only [card_empty, Nat.cast_zero]
    linarith

/-- The split-row inequality, with no restriction on how many times
a source row crosses target rows. -/
theorem split_rows_gap_bound {n N m B : ℕ} (hm : 1 ≤ m) (hB : 0 < B)
    (u v : Fin (n + 1) → ℕ) (hu : StrictMono u) (hv : StrictMono v)
    (hN : ∀ i, v i < N)
    (htags : ∀ i, (u i / B) % m = (v i / B) % m) :
    ((splitRows m B u v).card : ℝ) * (((m - 1) * B : ℕ) : ℝ) ≤
      (N : ℝ) - (n + 1) := by
  have hgap (i : Fin n) (hi : i ∈ splitTransitions m B u v) :
      ((((m - 1) * B : ℕ) : ℝ)) ≤
        (v i.succ : ℝ) - (v i.castSucc : ℝ) - 1 := by
    have hpair := (mem_filter.1 hi).2
    have hij : i.castSucc < i.succ := by simp
    have hvrow : v i.castSucc / B / m < v i.succ / B / m := by
      have hle : v i.castSucc / B / m ≤ v i.succ / B / m :=
        Nat.div_le_div_right (Nat.div_le_div_right (hv.monotone (le_of_lt hij)))
      exact lt_of_le_of_ne hle hpair.2
    have h := tagged_gap hm hB (hu.monotone (le_of_lt hij))
      hpair.1 hvrow (htags i.castSucc) (htags i.succ)
    have hc : (v i.castSucc : ℝ) + 1 + (((m - 1) * B : ℕ) : ℝ) ≤
        (v i.succ : ℝ) := by exact_mod_cast h
    linarith
  have hcount : (splitRows m B u v).card ≤ (splitTransitions m B u v).card :=
    card_image_le
  calc
    ((splitRows m B u v).card : ℝ) * (((m - 1) * B : ℕ) : ℝ) ≤
        ((splitTransitions m B u v).card : ℝ) * (((m - 1) * B : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast hcount
    _ ≤ (N : ℝ) - (n + 1) :=
      selected_gap_bound v hv hN (splitTransitions m B u v) _ hgap

/-- The algebraic conclusion of the split and nonsplit accounts, including
zero local deficit. -/
theorem harmonic_bound {E d g T s : ℝ} (hd : 0 ≤ d) (hg : 0 < g)
    (hunsplit : d * (T - s) ≤ E) (hsplit : s * g ≤ E) :
    T * d * g / (d + g) ≤ E := by
  have hden : 0 < d + g := by linarith
  apply (div_le_iff₀ hden).2
  have h1 := mul_le_mul_of_nonneg_left hunsplit (le_of_lt hg)
  have h2 := mul_le_mul_of_nonneg_left hsplit hd
  nlinarith

/-- The harmonic lower bound implies the convenient half-minimum form. -/
theorem half_min_le_harmonic {d g T : ℝ} (hd : 0 ≤ d) (hg : 0 < g)
    (hT : 0 ≤ T) :
    T / 2 * min d g ≤ T * d * g / (d + g) := by
  have hden : 0 < d + g := by linarith
  apply (le_div_iff₀ hden).2
  rcases le_total d g with h | h
  · rw [min_eq_left h]
    have hmul := mul_nonneg hT (mul_nonneg hd (sub_nonneg.mpr h))
    nlinarith
  · rw [min_eq_right h]
    have hmul := mul_nonneg hT (mul_nonneg (le_of_lt hg) (sub_nonneg.mpr h))
    nlinarith

/-- Empty matchings satisfy the same bound, using only the evident local
upper bound on the row deficit. -/
theorem harmonic_le_total {T d g W : ℝ} (hT : 0 ≤ T) (hd : 0 ≤ d)
    (hg : 0 < g) (hdW : d ≤ W) :
    T * d * g / (d + g) ≤ T * W := by
  have hden : 0 < d + g := by linarith
  calc
    T * d * g / (d + g) ≤ T * d := by
      apply (div_le_iff₀ hden).2
      have hnonneg := mul_nonneg hT (sq_nonneg d)
      nlinarith
    _ ≤ T * W := mul_le_mul_of_nonneg_left hdW hT

/-- The commonly used `Td/2` consequence, with its actual hypothesis. -/
theorem half_local_le_harmonic {d g T : ℝ} (hd : 0 ≤ d) (hg : 0 < g)
    (hT : 0 ≤ T) (hdg : d ≤ g) :
    T * d / 2 ≤ T * d * g / (d + g) := by
  have h := half_min_le_harmonic hd hg hT
  rw [min_eq_left hdg] at h
  linarith

end TreeEdit.BinaryLower.Tagged

end OAI
