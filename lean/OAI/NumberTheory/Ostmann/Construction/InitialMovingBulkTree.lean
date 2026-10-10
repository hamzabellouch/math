import OAI.NumberTheory.Ostmann.Construction.InitialMovingBulkLists

namespace OAI

/-! # The literal two half-bulk weights through every moving branch -/
namespace Ostmann
open scoped Classical BigOperators

def MovingLeafLengthEq {P : Type*} : (n : ℕ) → TreeLeafTuple (List P) n → ℕ → Prop
  | 0, x, r => (show List P from x).length = r
  | n + 1, x, r => MovingLeafLengthEq n x.1 r ∧ MovingLeafLengthEq n x.2 r

theorem moving_append_length_eq {P : Type*} (n : ℕ)
    (x y : TreeLeafTuple (List P) n) (a b : ℕ)
    (hx : MovingLeafLengthEq n x a) (hy : MovingLeafLengthEq n y b) :
    MovingLeafLengthEq n (appendMovingSlotLeaves n x y) (a + b) := by
  induction n with
  | zero => exact (List.length_append).trans (congrArg₂ (· + ·) hx hy)
  | succ n ih => exact ⟨ih x.1 y.1 hx.1 hy.1, ih x.2 y.2 hx.2 hy.2⟩

theorem moving_compensation_length_eq {P : Type*} (n : ℕ)
    (samples : TreeLeafTuple (Fin 4 → P) n) :
    MovingLeafLengthEq n (movingCompensationSlots n samples) 4 := by
  induction n with
  | zero => exact List.length_ofFn
  | succ n ih => exact ⟨ih samples.1, ih samples.2⟩

noncomputable def initialHalfBulkProduct {P : Type*} (value : P → ℕ)
    (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) :
    (n : ℕ) → (TreeLeafIndex n × Fin (b + b) → P) → ℝ
  | 0, slot => initialHalfBulkWeight value b d cb cd sl sr (fun i => slot ((), i))
  | n + 1, slot =>
      initialHalfBulkProduct value b d cb cd sl sr n (fun j => slot (.inl j.1, j.2)) *
      initialHalfBulkProduct value b d cb cd sl sr n (fun j => slot (.inr j.1, j.2))

theorem initialMovingTreeWeight_sample {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (n s : ℕ) (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P) (a : MovingSampleSlots P n)
    (hsmall : MovingLeafLengthEq n small s) (hlen : s + 4 * n = r + r) :
    initialMovingTreeWeight value b d r cb cd sl sr fallback
      (buildMovingSlotData n t small (bulkSlotLeaves n (b + b) slot) a) =
      initialHalfBulkProduct value b d cb cd sl sr n slot := by
  induction a generalizing s with
  | leaf =>
    change initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback ((show List P from small) ++ List.ofFn (fun i => slot ((), i)))) = _
    exact initialMovingRealWeight_list value b d r cb cd sl sr fallback small
      (hsmall.trans (by omega)) _
  | @node n samples left right ihL ihR =>
    have hl : 4 + s + 4 * n = r + r := by omega
    change initialMovingTreeWeight value b d r cb cd sl sr fallback
        (buildMovingSlotData n t.2.1
          (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.1)
          (bulkSlotLeaves n (b + b) (fun j => slot (.inl j.1, j.2))) left) *
      initialMovingTreeWeight value b d r cb cd sl sr fallback
        (buildMovingSlotData n t.2.2
          (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.2)
          (bulkSlotLeaves n (b + b) (fun j => slot (.inr j.1, j.2))) right) = _
    rw [ihL _ _ _ _ (moving_append_length_eq n _ _ 4 s
      (moving_compensation_length_eq n samples) hsmall.1) hl,
      ihR _ _ _ _ (moving_append_length_eq n _ _ 4 s
        (moving_compensation_length_eq n samples) hsmall.2) hl]
    rfl

end Ostmann

end OAI
