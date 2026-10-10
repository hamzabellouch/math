import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationReaderWork

namespace OAI

/-! # Reader accounting including every internal key evaluation

A supplied counted key is executed at each tournament comparison. The value
refinement is unconditional; the work theorem composes its finite cost
bound with the depth of the actually traversed replacement path.
-/

namespace LowSpaceSubsetSum
namespace Tournament

variable {α : Type*}

def measuredPick (key : α → ℤ × ℕ) : Option α → Option α → Option α × ℕ
  | none, v => (v, 1)
  | u, none => (u, 2)
  | some x, some y =>
    let a := key x
    let b := key y
    (if a.1 ≤ b.1 then some x else some y, a.2 + b.2 + 3)

theorem measuredPick_value (key : α → ℤ × ℕ) (u v : Option α) :
    (measuredPick key u v).1 = pick (fun x => (key x).1) u v := by
  cases u <;> cases v <;> rfl

theorem measuredPick_work (key : α → ℤ × ℕ) (K : ℕ)
    (hk : ∀ x, (key x).2 ≤ K) (u v : Option α) :
    (measuredPick key u v).2 ≤ 2 * K + 3 := by
  cases u with
  | none => simp only [measuredPick]; omega
  | some x =>
    cases v with
    | none => simp only [measuredPick]; omega
    | some y =>
      have hx := hk x
      have hy := hk y
      change (key x).2 + (key y).2 + 3 ≤ _
      omega

def measuredReplace (key : α → ℤ × ℕ) : {d : ℕ} → Tree α d →
    (Fin d → Bool) → Option α → Tree α d × ℕ
  | 0, .leaf _, _, v => (.leaf v, 2)
  | _d + 1, .node _ l r, path, v =>
    if path 0 then
      let a := measuredReplace key r (fun i => path i.succ) v
      let b := measuredPick key (winner l) (winner a.1)
      (.node b.1 l a.1, a.2 + b.2 + 5)
    else
      let a := measuredReplace key l (fun i => path i.succ) v
      let b := measuredPick key (winner a.1) (winner r)
      (.node b.1 a.1 r, a.2 + b.2 + 5)

theorem measuredReplace_value (key : α → ℤ × ℕ) {d : ℕ} (t : Tree α d)
    (path : Fin d → Bool) (v : Option α) :
    (measuredReplace key t path v).1 = replace (fun x => (key x).1) t path v := by
  induction t with
  | leaf _ => rfl
  | node _ l r ihl ihr =>
    simp only [measuredReplace, replace]
    split <;> simp only [measuredPick_value, ihl, ihr, node]

theorem measuredReplace_work (key : α → ℤ × ℕ) (K : ℕ)
    (hk : ∀ x, (key x).2 ≤ K) {d : ℕ} (t : Tree α d)
    (path : Fin d → Bool) (v : Option α) :
    (measuredReplace key t path v).2 ≤ (2 * K + 8) * d + 2 := by
  induction t with
  | leaf _ => simp only [measuredReplace, Nat.mul_zero, Nat.zero_add]; rfl
  | @node d _ l r ihl ihr =>
    simp only [measuredReplace]
    split
    · have hp := measuredPick_work key K hk (winner l)
        (winner (measuredReplace key r (fun i => path i.succ) v).1)
      have hi := ihr (fun i => path i.succ)
      dsimp only at hi ⊢
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    · have hp := measuredPick_work key K hk
        (winner (measuredReplace key l (fun i => path i.succ) v).1) (winner r)
      have hi := ihl (fun i => path i.succ)
      dsimp only at hi ⊢
      simp only [Nat.mul_add, Nat.mul_one]
      omega

end Tournament

namespace RowMerge

variable {α σ : Type*} {d : ℕ}

def measuredAdvance (key : α → ℤ × ℕ) (read : σ → Option (α × σ) × ℕ)
    (t : Tournament.Tree (Front d α σ) d) :
    Option (α × Tournament.Tree (Front d α σ) d) × ℕ :=
  match Tournament.winner t with
  | none => (none, 2)
  | some x =>
    let a := read x.after
    let v := a.1.map (fun z => (⟨x.row, z.1, z.2⟩ : Front d α σ))
    let b := Tournament.measuredReplace (fun y => key y.value) t x.row v
    (some (x.value, b.1), a.2 + b.2 + 8)

theorem measuredAdvance_value (key : α → ℤ × ℕ) (read : σ → Option (α × σ) × ℕ)
    (t : Tournament.Tree (Front d α σ) d) :
    (measuredAdvance key read t).1 = advance (fun x => (key x).1) (fun s => (read s).1) t := by
  unfold measuredAdvance advance
  cases Tournament.winner t with
  | none => rfl
  | some x => simp only [Tournament.measuredReplace_value, front, Option.map_some]

theorem measuredAdvance_work (key : α → ℤ × ℕ) (read : σ → Option (α × σ) × ℕ)
    (K R : ℕ) (hk : ∀ x, (key x).2 ≤ K) (hr : ∀ s, (read s).2 ≤ R)
    (t : Tournament.Tree (Front d α σ) d) :
    (measuredAdvance key read t).2 ≤ R + (2 * K + 8) * d + 10 := by
  unfold measuredAdvance
  cases hw : Tournament.winner t with
  | none => simp only; omega
  | some x =>
    have hb := Tournament.measuredReplace_work (fun y : Front d α σ => key y.value)
      K (fun y => hk y.value) t x.row
      ((read x.after).1.map (fun z => (⟨x.row, z.1, z.2⟩ : Front d α σ)))
    have ha := hr x.after
    change _ + _ + 8 ≤ _
    omega

end RowMerge

namespace MergedReader

variable {α σ : Type*} {d : ℕ}

def measuredNext (key : α → ℤ × ℕ) (read : σ → Option (α × σ) × ℕ)
    (view : σ → List α) (hread : RowMerge.IsReader (fun s => (read s).1) view)
    (s : State (fun x => (key x).1) view d) :
    Option (α × State (fun x => (key x).1) view d) × ℕ :=
  let q := RowMerge.measuredAdvance key read s.tree
  match hq : q.1 with
  | none => (none, q.2)
  | some (a, t) =>
    have ha : RowMerge.advance (fun x => (key x).1) (fun s => (read s).1) s.tree = some (a, t) :=
      (RowMerge.measuredAdvance_value key read s.tree).symm.trans hq
    (some (a, ⟨t, RowMerge.advance_valid _ _ s.tree s.valid ha,
      RowMerge.advance_aligned _ _ s.tree s.aligned ha,
      advance_sorted _ _ view hread s ha⟩), q.2)

theorem measuredNext_value (key : α → ℤ × ℕ) (read : σ → Option (α × σ) × ℕ)
    (view : σ → List α) (hread : RowMerge.IsReader (fun s => (read s).1) view)
    (s : State (fun x => (key x).1) view d) :
    (measuredNext key read view hread s).1 =
      next (fun x => (key x).1) (fun s => (read s).1) view hread s := by
  unfold measuredNext
  dsimp only
  split
  · rename_i hq
    exact (next_none _ _ view hread s
      ((RowMerge.measuredAdvance_value key read s.tree).symm.trans hq)).symm
  · rename_i a t hq
    exact (next_some _ _ view hread s
      ((RowMerge.measuredAdvance_value key read s.tree).symm.trans hq)).symm

theorem measuredNext_work (key : α → ℤ × ℕ) (read : σ → Option (α × σ) × ℕ)
    (view : σ → List α) (hread : RowMerge.IsReader (fun s => (read s).1) view)
    (s : State (fun x => (key x).1) view d)
    (K R : ℕ) (hk : ∀ x, (key x).2 ≤ K) (hr : ∀ s, (read s).2 ≤ R) :
    (measuredNext key read view hread s).2 ≤ R + (2 * K + 8) * d + 10 := by
  have hw := RowMerge.measuredAdvance_work key read K R hk hr s.tree
  unfold measuredNext
  dsimp only
  split <;> exact hw

end MergedReader
end LowSpaceSubsetSum

end OAI
