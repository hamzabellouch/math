import OAI.NumberTheory.TwoPoint.Circuits.CircuitBlockCode
import Mathlib.Data.List.OfFn

namespace OAI

/-! The finite alphabet for query positions and responses. Allowing one
separator per block at most doubles the length of a query code. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

abbrev BoundedRestrictionCode (w k : ℕ) :=
  Σ l : Fin (k + 1), Fin l.val → Option (Fin (w + 1) × Bool)

def readRestrictionCode {w k : ℕ} (c : BoundedRestrictionCode w k) :
    List (Option (ℕ × Bool)) :=
  List.ofFn (fun i => (c.2 i).map (fun z => (z.1.val, z.2)))

noncomputable def packRestrictionSymbol (w : ℕ) (z : Option (ℕ × Bool))
    (hz : ∀ a b, z = some (a, b) → a ≤ w) : Option (Fin (w + 1) × Bool) :=
  match z with
  | none => none
  | some (a, b) => some (⟨a, Nat.lt_succ_of_le (hz a b rfl)⟩, b)

lemma read_packRestrictionSymbol (w : ℕ) (z : Option (ℕ × Bool))
    (hz : ∀ a b, z = some (a, b) → a ≤ w) :
    (packRestrictionSymbol w z hz).map (fun v => (v.1.val, v.2)) = z := by
  cases z with
  | none => rfl
  | some z => cases z; rfl

noncomputable def packRestrictionCode (w k : ℕ) (l : List (Option (ℕ × Bool)))
    (hl : l.length ≤ k)
    (hw : ∀ z ∈ l, ∀ a b, z = some (a, b) → a ≤ w) : BoundedRestrictionCode w k :=
  ⟨⟨l.length, Nat.lt_succ_of_le hl⟩, fun i => packRestrictionSymbol w (l.get i)
    (hw (l.get i) (List.get_mem l i))⟩

lemma read_packRestrictionCode (w k : ℕ) (l : List (Option (ℕ × Bool)))
    (hl : l.length ≤ k)
    (hw : ∀ z ∈ l, ∀ a b, z = some (a, b) → a ≤ w) :
    readRestrictionCode (packRestrictionCode w k l hl hw) = l := by
  unfold readRestrictionCode packRestrictionCode
  simp only [read_packRestrictionSymbol]
  exact List.ofFn_get l

lemma boundedRestrictionCode_card (w k : ℕ) :
    Fintype.card (BoundedRestrictionCode w k) ≤ (k + 1) * (2 * w + 3) ^ k := by
  rw [Fintype.card_sigma]
  calc
    _ = ∑ l : Fin (k + 1), (2 * w + 3) ^ l.val := by
      apply sum_congr rfl
      intro l _
      simp [Nat.add_mul, Nat.mul_comm, Nat.add_assoc]
    _ ≤ ∑ _l : Fin (k + 1), (2 * w + 3) ^ k := by
      apply sum_le_sum
      intro l _
      exact Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ l.isLt)
    _ = _ := by simp

lemma two_mul_add_one_le_three_pow (h : ℕ) : 2 * h + 1 ≤ 3 ^ h := by
  induction h with
  | zero => norm_num
  | succ h ih =>
    have hp : 1 ≤ 3 ^ h := Nat.one_le_pow h 3 (by omega)
    rw [pow_succ]
    omega

lemma boundedRestrictionCode_card_queries (w h : ℕ) :
    Fintype.card (BoundedRestrictionCode w (2 * h)) ≤
      (3 * (2 * w + 3) ^ 2) ^ h := by
  apply (boundedRestrictionCode_card w (2 * h)).trans
  calc
    (2 * h + 1) * (2 * w + 3) ^ (2 * h) ≤ 3 ^ h * (2 * w + 3) ^ (2 * h) :=
      Nat.mul_le_mul_right _ (two_mul_add_one_le_three_pow h)
    _ = _ := by rw [mul_pow, ← pow_mul]

end TwoPointCorrelations

end OAI
