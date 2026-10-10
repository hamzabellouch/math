import Mathlib

namespace OAI

section
section
namespace CriticalPercolation.BinaryInterpolation
open scoped Classical

def midpoint (l r : ℕ) : ℕ := (l+r)/2

def bisect (l r : ℕ) (side : Bool) : ℕ × ℕ :=
  if r ≤ l+1 then (l,r) else if side then (midpoint l r,r) else (l,midpoint l r)

lemma midpoint_strict {l r : ℕ} (h : l+1 < r) :
    l < midpoint l r ∧ midpoint l r < r := by
  dsimp [midpoint]
  omega

lemma bisect_bounds {l r : ℕ} (h : l < r) (b : Bool) :
    l ≤ (bisect l r b).1 ∧ (bisect l r b).1 < (bisect l r b).2 ∧
      (bisect l r b).2 ≤ r := by
  unfold bisect
  split_ifs with ht hb
  · simp [h]
  · have hm := midpoint_strict (by omega : l+1 < r)
    simp only
    omega
  · have hm := midpoint_strict (by omega : l+1 < r)
    simp only
    omega

lemma bisect_length {l r : ℕ} (h : l+1 < r) (b : Bool) :
    (bisect l r b).2 - (bisect l r b).1 ≤ (r-l+1)/2 := by
  unfold bisect
  rw [ite_eq_right (by omega : ¬ r ≤ l+1)]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte,midpoint] <;> omega

lemma bisect_clog {l r : ℕ} (h : l+1 < r) (b : Bool) :
    Nat.clog 2 ((bisect l r b).2 - (bisect l r b).1) + 1 ≤ Nat.clog 2 (r-l) := by
  have hh := Nat.clog_mono_right 2 (bisect_length h b)
  rw [Nat.clog_of_one_lt (by decide : 1 < 2) (by omega : 1 < r-l)]
  have he : r-l+2-1 = r-l+1 := by omega
  rw [he]
  exact Nat.add_le_add_right hh 1

def terminal (l r : ℕ) : List Bool → ℕ × ℕ
  | [] => (l,r)
  | b::bs => terminal (bisect l r b).1 (bisect l r b).2 bs

lemma terminal_bounds {l r : ℕ} (h : l < r) (bs : List Bool) :
    l ≤ (terminal l r bs).1 ∧ (terminal l r bs).1 < (terminal l r bs).2 ∧
      (terminal l r bs).2 ≤ r := by
  induction bs generalizing l r with
  | nil => simpa [terminal] using h
  | cons b bs ih =>
    have hb := bisect_bounds h b
    have hi := ih hb.2.1
    change l ≤ (terminal (bisect l r b).1 (bisect l r b).2 bs).1 ∧ _
    exact ⟨hb.1.trans hi.1,hi.2.1,hi.2.2.trans hb.2.2⟩

lemma terminal_eq_of_adjacent {l r : ℕ} (h : r = l+1) (bs : List Bool) :
    terminal l r bs = (l,r) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa only [terminal,bisect,ite_eq_left (by omega : r ≤ l+1)] using ih

theorem terminal_adjacent {l r : ℕ} (h : l < r) (bs : List Bool)
    (hlen : Nat.clog 2 (r-l) ≤ bs.length) :
    (terminal l r bs).2 = (terminal l r bs).1 + 1 := by
  induction bs generalizing l r with
  | nil =>
    simp only [List.length_nil] at hlen
    have hh := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp hlen
    simp only [pow_zero] at hh
    simp only [terminal]
    omega
  | cons b bs ih =>
    by_cases ht : r ≤ l+1
    · rw [terminal_eq_of_adjacent (by omega : r = l+1)]
      dsimp only
      omega
    · have hb := bisect_bounds h b
      have hc := bisect_clog (by omega : l+1 < r) b
      simp only [List.length_cons] at hlen
      exact ih hb.2.1 (by omega)

def anchors (l r : ℕ) : List Bool → Finset ℕ
  | [] => {l,r}
  | b::bs => {l,r,midpoint l r} ∪ anchors (bisect l r b).1 (bisect l r b).2 bs

lemma terminal_mem_anchors (l r : ℕ) (bs : List Bool) :
    (terminal l r bs).1 ∈ anchors l r bs ∧ (terminal l r bs).2 ∈ anchors l r bs := by
  induction bs generalizing l r with
  | nil => simp [terminal,anchors]
  | cons b bs ih =>
    exact ⟨Finset.mem_union_right _ (ih _ _).1, Finset.mem_union_right _ (ih _ _).2⟩

lemma midpoint_internal {d l r : ℕ} (_hl : l ≤ r) (hr : r ≤ d) (h : l+1 < r) :
    midpoint l r < d ∧ 0 < midpoint l r ∧ midpoint l r-l < d ∧ r-midpoint l r < d := by
  have hm := midpoint_strict h
  omega

abbrev Descriptor (J : ℕ) := (n : Fin (J+1)) × (Fin n.val → Fin 8)

lemma descriptor_card (J : ℕ) : Fintype.card (Descriptor J) = ∑ j ∈ Finset.range (J+1), 8^j := by
  simp only [Descriptor,Fintype.card_sigma,Fintype.card_fun,Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun j => 8^j) (J+1)

lemma descriptor_card_le (J : ℕ) : Fintype.card (Descriptor J) ≤ 8^(J+1) := by
  rw [descriptor_card]
  have hh : ∀ n : ℕ, (∑ j ∈ Finset.range n, 8^j) < 8^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,pow_succ]; omega
  exact (hh (J+1)).le

end CriticalPercolation.BinaryInterpolation
end
end

end OAI
