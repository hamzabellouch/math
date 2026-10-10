import OAI.Combinatorics.BinaryEdit.TaggedGaps
import OAI.Combinatorics.BinaryEdit.TaggedNonsplit
import OAI.Combinatorics.BinaryEdit.BlockRestriction
import OAI.Combinatorics.BinaryEdit.LCS

namespace OAI

/-! The numeric and list-slice forms of the ordered-tag alignment lemma.
These statements allow arbitrary increasing matchings across row boundaries. -/

namespace TreeEdit.BinaryLower.Tagged

open Finset

/-- Complete ordered-tag accounting for an arbitrary increasing matching.
The local bound counts matches in a whole source/target row pair. -/
theorem numeric_alignment_bound {L T m B : ℕ} (hm : 2 ≤ m) (hB : 0 < B)
    (u v : Fin L → ℕ) (hu : StrictMono u) (hv : StrictMono v)
    (hub : ∀ i, u i < T * m * B) (hvb : ∀ i, v i < T * m * B)
    (htags : ∀ i, u i / B % m = v i / B % m)
    (d : ℝ) (hd : 0 ≤ d) (hdW : d ≤ (m * B : ℕ))
    (hlocal : ∀ a < T, ∀ b < T,
      ((univ.filter fun i : Fin L =>
        u i / B / m = a ∧ v i / B / m = b).card : ℝ) ≤ (m * B : ℕ) - d) :
    (T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
        (d + (((m - 1) * B : ℕ) : ℝ)) ≤
      (T * m * B : ℕ) - (L : ℝ) := by
  have hmpos : 0 < m := by omega
  have hg : 0 < (((m - 1) * B : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (show 0 < m - 1 by omega) hB
  have hL : L ≤ T * m * B := by
    calc
      L = (univ : Finset (Fin L)).card := by simp
      _ ≤ (range (T * m * B)).card := by
        apply card_le_card_of_injOn u
        · intro i _
          exact mem_range.mpr (hub i)
        · intro i _ j _ hij
          exact hu.injective hij
      _ = T * m * B := card_range _
  cases L with
  | zero =>
      have h := harmonic_le_total (Nat.cast_nonneg T) hd hg hdW
      simpa only [Nat.cast_zero, sub_zero, Nat.cast_mul, mul_assoc] using h
  | succ n =>
      have hnonsplit := TaggedNonsplit.nonsplit_loss_numeric u hu.injective hmpos hB hub
        (splitRows m B u v) (splitRows_subset_range hmpos hB u v hub) d
        (fun a ha haS => nonsplit_row_card_le hmpos hB u v hu.monotone hvb d hdW
          hlocal ha haS)
      rw [Nat.cast_sub hL] at hnonsplit
      simp only [Nat.cast_add, Nat.cast_one] at hnonsplit
      have hsplit := split_rows_gap_bound (by omega) hB u v hu hv hvb htags
      have h := harmonic_bound hd hg hnonsplit hsplit
      simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one] using h

/-- Core list version: local row-pair LCS loss and ordered disjoint tags imply
the global harmonic lower bound. Slices are literal contiguous rows of width
`m * B`, and all intermediate subsequence matchings remain unrestricted. -/
theorem tagged_slice_alignment {α : Type*} {T m B : ℕ}
    (hT : 0 < T) (hm : 2 ≤ m) (hB : 0 < B)
    (x y : List α) (hx : x.length = T * m * B) (hy : y.length = T * m * B)
    (htags : ∀ p (hp : p < x.length) q (hq : q < y.length),
      x[p]'hp = y[q]'hq → p / B % m = q / B % m)
    (d : ℝ) (hd : 0 ≤ d)
    (hlocal : ∀ a < T, ∀ b < T,
      (lcs ((x.drop (a * (m * B))).take (m * B))
        ((y.drop (b * (m * B))).take (m * B)) : ℝ) ≤ (m * B : ℕ) - d) :
    (T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
        (d + (((m - 1) * B : ℕ) : ℝ)) ≤
      (deficit (T * m * B) x y : ℝ) := by
  have hmpos : 0 < m := by omega
  have hdW : d ≤ (m * B : ℕ) := by
    have h := hlocal 0 hT 0 hT
    have hnonneg : 0 ≤ (lcs ((x.drop (0 * (m * B))).take (m * B))
        ((y.drop (0 * (m * B))).take (m * B)) : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨⟨f, g, hmatch⟩⟩ := exists_lcs_alignment x y
  let u : Fin (lcs x y) → ℕ := fun i => (f i).val
  let v : Fin (lcs x y) → ℕ := fun i => (g i).val
  have hu : StrictMono u := by
    intro i j hij
    exact f.strictMono hij
  have hv : StrictMono v := by
    intro i j hij
    exact g.strictMono hij
  have hxu : ∀ i, u i < x.length := fun i => (f i).isLt
  have hyv : ∀ i, v i < y.length := fun i => (g i).isLt
  have hub : ∀ i, u i < T * m * B := by simpa only [hx] using hxu
  have hvb : ∀ i, v i < T * m * B := by simpa only [hy] using hyv
  have heq : ∀ i, x[u i]'(hxu i) = y[v i]'(hyv i) := by
    intro i
    simpa only [u, v, List.get_eq_getElem] using hmatch i
  have htagmatch : ∀ i, u i / B % m = v i / B % m := by
    intro i
    exact htags _ (hxu i) _ (hyv i) (heq i)
  have hlocalmatch : ∀ a < T, ∀ b < T,
      ((univ.filter fun i : Fin (lcs x y) =>
        u i / B / m = a ∧ v i / B / m = b).card : ℝ) ≤ (m * B : ℕ) - d := by
    intro a ha b hb
    have h := BlockRestriction.card_filter_rows_le_lcs x y u v hu hv hxu hyv heq
      m B a b hmpos hB
    exact (Nat.cast_le.mpr h).trans (hlocal a ha b hb)
  have h := numeric_alignment_bound hm hB u v hu hv hub hvb htagmatch d hd hdW hlocalmatch
  have hlcs : lcs x y ≤ T * m * B := by simpa only [hx] using lcs_le_length_left x y
  simpa only [deficit, Nat.cast_sub hlcs] using h

end TreeEdit.BinaryLower.Tagged

end OAI
