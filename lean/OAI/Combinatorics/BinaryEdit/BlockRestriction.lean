import OAI.Combinatorics.BinaryEdit.MatchingSublist
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

namespace OAI

/-! Restricting increasing common matchings to arbitrary contiguous intervals. -/

namespace TreeEdit.BinaryLower
namespace BlockRestriction

universe u
variable {α : Type u}

/-- Restriction to any selected set of matched pairs lying in two specified
intervals has size at most the LCS of the corresponding list slices.
The intervals may touch or exceed the list boundary; no artificial positivity
or nonempty-matching assumption is needed. -/
theorem card_le_lcs_slices (x y : List α) {n : ℕ}
    (u v : Fin n → ℕ) (hu : StrictMono u) (hv : StrictMono v)
    (hxu : ∀ t, u t < x.length) (hyv : ∀ t, v t < y.length)
    (heq : ∀ t, x[u t]'(hxu t) = y[v t]'(hyv t))
    (s : Finset (Fin n)) (a b A B : ℕ)
    (hsu : ∀ t ∈ s, a ≤ u t ∧ u t < a + A)
    (hsv : ∀ t ∈ s, b ≤ v t ∧ v t < b + B) :
    s.card ≤ lcs ((x.drop a).take A) ((y.drop b).take B) := by
  let e : Fin s.card ↪o Fin n := s.orderEmbOfFin rfl
  have he (i : Fin s.card) : e i ∈ s := s.orderEmbOfFin_mem rfl i
  let ui : Fin s.card → Fin ((x.drop a).take A).length := fun i =>
    ⟨u (e i) - a, by
      have h₁ := hsu (e i) (he i)
      have h₂ := hxu (e i)
      simp only [List.length_take, List.length_drop]
      omega⟩
  let vi : Fin s.card → Fin ((y.drop b).take B).length := fun i =>
    ⟨v (e i) - b, by
      have h₁ := hsv (e i) (he i)
      have h₂ := hyv (e i)
      simp only [List.length_take, List.length_drop]
      omega⟩
  have hui : StrictMono ui := by
    intro i j hij
    have hlt := hu (e.strictMono hij)
    have hi := (hsu (e i) (he i)).1
    change u (e i) - a < u (e j) - a
    omega
  have hvi : StrictMono vi := by
    intro i j hij
    have hlt := hv (e.strictMono hij)
    have hi := (hsv (e i) (he i)).1
    change v (e i) - b < v (e j) - b
    omega
  apply TreeEdit.BinaryLower.matching_length_le_lcs _ _ ui vi hui hvi
  intro i
  have hua := (hsu (e i) (he i)).1
  have hvb := (hsv (e i) (he i)).1
  simpa only [ui, vi, List.get_eq_getElem, List.getElem_take,
    List.getElem_drop, Nat.add_sub_of_le hua, Nat.add_sub_of_le hvb]
    using heq (e i)

/-- The quotient convention in the tagged-row proof identifies a contiguous
interval of width `m * B`; the order `p / B / m` is retained literally. -/
lemma row_bounds {p m B r : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hrow : p / B / m = r) :
    r * (m * B) ≤ p ∧ p < r * (m * B) + m * B := by
  have hp : p / (m * B) = r := by
    simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm B m] using hrow
  have hbounds := (Nat.div_eq_iff (Nat.mul_pos hm hB)).mp hp
  have hpos := Nat.mul_pos hm hB
  omega

/-- The exact row-pair restriction used in ordered-tag matching arguments.
No row-boundary alignment of the original matching is assumed. -/
theorem card_filter_rows_le_lcs (x y : List α) {n : ℕ}
    (u v : Fin n → ℕ) (hu : StrictMono u) (hv : StrictMono v)
    (hxu : ∀ t, u t < x.length) (hyv : ∀ t, v t < y.length)
    (heq : ∀ t, x[u t]'(hxu t) = y[v t]'(hyv t))
    (m B a b : ℕ) (hm : 0 < m) (hB : 0 < B) :
    (Finset.univ.filter (fun t => u t / B / m = a ∧ v t / B / m = b)).card ≤
      lcs ((x.drop (a * (m * B))).take (m * B))
        ((y.drop (b * (m * B))).take (m * B)) := by
  apply card_le_lcs_slices x y u v hu hv hxu hyv heq
  · intro t ht
    have hrow := ((Finset.mem_filter.mp ht).2).1
    exact row_bounds hm hB hrow
  · intro t ht
    have hrow := ((Finset.mem_filter.mp ht).2).2
    exact row_bounds hm hB hrow

end BlockRestriction
end TreeEdit.BinaryLower

end OAI
