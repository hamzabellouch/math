import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace OAI

namespace Zarankiewicz
open Finset

def lowerTriangle (s : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (s+1)) ×ˢ (Icc 1 (s+1))).filter (fun z => z.2 < z.1)

def upperTriangle (s : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc (s+2) (2*s+1)) ×ˢ (Icc (s+2) (2*s+1))).filter (fun z => z.1 < z.2)

def twoTriangle (s : ℕ) : Finset (ℕ × ℕ) := lowerTriangle s ∪ upperTriangle s

theorem mem_lowerTriangle (s p q : ℕ) :
    (p,q) ∈ lowerTriangle s ↔ 1 ≤ q ∧ q < p ∧ p ≤ s+1 := by
  simp only [lowerTriangle, mem_filter, mem_product, mem_Icc]
  omega

theorem mem_upperTriangle (s p q : ℕ) :
    (p,q) ∈ upperTriangle s ↔ s+1 < p ∧ p < q ∧ q ≤ 2*s+1 := by
  simp only [upperTriangle, mem_filter, mem_product, mem_Icc]
  omega

theorem mem_twoTriangle (s p q : ℕ) :
    (p,q) ∈ twoTriangle s ↔
      (1 ≤ q ∧ q < p ∧ p ≤ s+1) ∨ (s+1 < p ∧ p < q ∧ q ≤ 2*s+1) := by
  rw [twoTriangle, mem_union, mem_lowerTriangle, mem_upperTriangle]

theorem disjoint_triangles (s : ℕ) : Disjoint (lowerTriangle s) (upperTriangle s) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨p,q⟩ hp hq
  rw [mem_lowerTriangle] at hp
  rw [mem_upperTriangle] at hq
  omega

theorem card_lowerTriangle (s : ℕ) : (lowerTriangle s).card = (s+1).choose 2 := by
  have hswap : (lowerTriangle s).card =
      (((Icc 1 (s+1)) ×ˢ (Icc 1 (s+1))).filter (fun z => z.1 < z.2)).card :=
    Finset.card_equiv (Equiv.prodComm ℕ ℕ) (by
      intro z
      simp [lowerTriangle, and_comm, and_left_comm, and_assoc])
  rw [hswap, Finset.card_product_filter_lt]
  simp

theorem card_upperTriangle (s : ℕ) : (upperTriangle s).card = s.choose 2 := by
  have h := Finset.card_product_filter_lt (s := Icc (s+2) (2*s+1))
  have hc : (Icc (s+2) (2*s+1)).card = s := by simp; omega
  simpa [upperTriangle, hc] using h

theorem adjacent_choose_two (s : ℕ) : (s+1).choose 2 + s.choose 2 = s*s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have ha : (s+2).choose 2 = (s+1).choose 2 + (s+1) := by
      calc
        (s+2).choose 2 = (s+1).choose 1 + (s+1).choose 2 := Nat.choose_succ_succ (s+1) 1
        _ = (s+1).choose 2 + (s+1) := by rw [Nat.choose_one_right]; omega
    have hb : (s+1).choose 2 = s.choose 2 + s := by
      simpa [Nat.choose_one_right, Nat.succ_eq_add_one, Nat.add_comm] using
        (Nat.choose_succ_succ s 1)
    have : s+1+1 = s+2 := by omega
    rw [this, ha]
    nlinarith

theorem card_twoTriangle (s : ℕ) : (twoTriangle s).card = s*s := by
  rw [twoTriangle, card_union_of_disjoint (disjoint_triangles s), card_lowerTriangle,
    card_upperTriangle, adjacent_choose_two]

def triangleRelabel (s k : ℕ) : ℕ := if k ≤ s then s+1+k else k-s+1

theorem triangleRelabel_injective_on (s : ℕ) :
    Set.InjOn (triangleRelabel s) (Set.Icc 1 (2*s-1)) := by
  intro p hp q hq he
  simp only [Set.mem_Icc] at hp hq
  unfold triangleRelabel at he
  split_ifs at he <;> omega

theorem triangleRelabel_range (s k : ℕ) (hk : k ∈ Icc 1 (2*s-1)) :
    triangleRelabel s k ∈ Icc 1 (2*s+1) ∧
      triangleRelabel s k ≠ s+1 ∧ triangleRelabel s k ≠ 1 := by
  simp only [mem_Icc] at hk ⊢
  unfold triangleRelabel
  split_ifs <;> omega

theorem relabel_twoTriangle (s : ℕ) (hs : 1 ≤ s) (p q : ℕ)
    (hpq : (p,q) ∈ twoTriangle (s-1)) :
    (triangleRelabel s q, triangleRelabel s p) ∈ twoTriangle s ∧
      triangleRelabel s q ≠ s+1 ∧ triangleRelabel s p ≠ 1 := by
  rw [mem_twoTriangle] at hpq ⊢
  unfold triangleRelabel
  split_ifs <;> omega

end Zarankiewicz

end OAI
