import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationKeyCells

namespace OAI

/-! # Live cells of tournament path replacement

The input tree and its untouched siblings remain shared. Each recursive
frame retains one path position; the trace includes both the old tree and
the new path while keys are evaluated. It never materializes candidate lists.
-/

namespace LowSpaceSubsetSum.MeasuredReaderCells

variable {α σ : Type*}

def pick (key : α → (ℤ × ℕ) × ℕ) : Option α → Option α → (Option α × ℕ) × ℕ
  | none, v => ((v, 1), 4)
  | u, none => ((u, 2), 4)
  | some x, some y =>
    let a := key x
    let b := key y
    ((if a.1.1 ≤ b.1.1 then some x else some y, a.1.2 + b.1.2 + 3), max a.2 b.2 + 8)

theorem pick_value (key : α → (ℤ × ℕ) × ℕ) (u v : Option α) :
    (pick key u v).1 = Tournament.measuredPick (fun x => (key x).1) u v := by
  cases u <;> cases v <;> rfl

theorem pick_cells (key : α → (ℤ × ℕ) × ℕ) (K : ℕ)
    (hk : ∀ x, (key x).2 ≤ K) (u v : Option α) : (pick key u v).2 ≤ K + 8 := by
  cases u with
  | none => simp only [pick]; omega
  | some x =>
    cases v with
    | none => simp only [pick]; omega
    | some y =>
      have hx := hk x
      have hy := hk y
      change max _ _ + 8 ≤ _
      omega

def replace (N : ℕ) (key : α → (ℤ × ℕ) × ℕ) : {d : ℕ} → Tournament.Tree α d →
    (Fin d → Bool) → Option α → (Tournament.Tree α d × ℕ) × ℕ
  | 0, .leaf _, _, v => ((.leaf v, 2), 2 * N + 8)
  | _d + 1, t@(.node _ l r), path, v =>
    let held := N * (Tournament.nodes t + 1)
    if path 0 then
      let a := replace N key r (fun i => path i.succ) v
      let b := pick key (Tournament.winner l) (Tournament.winner a.1.1)
      ((.node b.1.1 l a.1.1, a.1.2 + b.1.2 + 5),
        max (a.2 + held + 8) (b.2 + 2 * held + 8))
    else
      let a := replace N key l (fun i => path i.succ) v
      let b := pick key (Tournament.winner a.1.1) (Tournament.winner r)
      ((.node b.1.1 a.1.1 r, a.1.2 + b.1.2 + 5),
        max (a.2 + held + 8) (b.2 + 2 * held + 8))

theorem replace_value (N : ℕ) (key : α → (ℤ × ℕ) × ℕ) {d : ℕ}
    (t : Tournament.Tree α d) (path : Fin d → Bool) (v : Option α) :
    (replace N key t path v).1 = Tournament.measuredReplace (fun x => (key x).1) t path v := by
  induction t with
  | leaf _ => rfl
  | node _ l r ihl ihr =>
    simp only [replace, Tournament.measuredReplace]
    split <;> simp only [pick_value, ihl, ihr]

private theorem replace_step_bound (N K d c p : ℕ)
    (hc : c ≤ (d + 1) * (4 * (N * 2 ^ (d + 1)) + K + 40)) (hp : p ≤ K + 8) :
    max (c + N * 2 ^ (d + 2) + 8) (p + 2 * (N * 2 ^ (d + 2)) + 8) ≤
      (d + 2) * (4 * (N * 2 ^ (d + 2)) + K + 40) := by
  have hm : N * 2 ^ (d + 1) ≤ N * 2 ^ (d + 2) :=
    Nat.mul_le_mul_left N (Nat.pow_le_pow_right (by decide) (by omega))
  have hcoef : 4 * (N * 2 ^ (d + 1)) + K + 40 ≤
      4 * (N * 2 ^ (d + 2)) + K + 40 := by omega
  have hi := hc.trans (Nat.mul_le_mul_left (d + 1) hcoef)
  simp only [Nat.add_mul, Nat.one_mul] at hi ⊢
  omega

theorem replace_cells (N : ℕ) (key : α → (ℤ × ℕ) × ℕ) (K : ℕ)
    (hk : ∀ x, (key x).2 ≤ K) {d : ℕ} (t : Tournament.Tree α d)
    (path : Fin d → Bool) (v : Option α) :
    (replace N key t path v).2 ≤ (d + 1) * (4 * (N * 2 ^ (d + 1)) + K + 40) := by
  induction t with
  | leaf _ => simp only [replace]; norm_num; omega
  | @node d w l r ihl ihr =>
    have he : Tournament.nodes (Tournament.Tree.node w l r) + 1 = 2 ^ (d + 2) :=
      Tournament.nodes_exact _
    simp only [replace, he]
    split
    · exact replace_step_bound N K d _ _ (ihr (fun i => path i.succ))
        (pick_cells key K hk _ _)
    · exact replace_step_bound N K d _ _ (ihl (fun i => path i.succ))
        (pick_cells key K hk _ _)

def advance (N : ℕ) (key : α → (ℤ × ℕ) × ℕ)
    (read : σ → (Option (α × σ) × ℕ) × ℕ) {d : ℕ}
    (t : Tournament.Tree (RowMerge.Front d α σ) d) :
    (Option (α × Tournament.Tree (RowMerge.Front d α σ) d) × ℕ) × ℕ :=
  match Tournament.winner t with
  | none => ((none, 2), N * (Tournament.nodes t + 1) + 8)
  | some x =>
    let a := read x.after
    let v := a.1.1.map (fun z => (⟨x.row, z.1, z.2⟩ : RowMerge.Front d α σ))
    let b := replace N (fun y => key y.value) t x.row v
    ((some (x.value, b.1.1), a.1.2 + b.1.2 + 8),
      max (N * (Tournament.nodes t + 1) + a.2 + N + 8)
        (b.2 + N * (Tournament.nodes t + 1) + N + 8))

theorem advance_value (N : ℕ) (key : α → (ℤ × ℕ) × ℕ)
    (read : σ → (Option (α × σ) × ℕ) × ℕ) {d : ℕ}
    (t : Tournament.Tree (RowMerge.Front d α σ) d) :
    (advance N key read t).1 =
      RowMerge.measuredAdvance (fun x => (key x).1) (fun s => (read s).1) t := by
  unfold advance RowMerge.measuredAdvance
  cases Tournament.winner t with
  | none => rfl
  | some x => simp only [replace_value]

theorem advance_cells (N : ℕ) (key : α → (ℤ × ℕ) × ℕ)
    (read : σ → (Option (α × σ) × ℕ) × ℕ) (K R : ℕ)
    (hk : ∀ x, (key x).2 ≤ K) (hr : ∀ s, (read s).2 ≤ R) {d : ℕ}
    (t : Tournament.Tree (RowMerge.Front d α σ) d) :
    (advance N key read t).2 ≤ (d + 2) * (6 * (N * 2 ^ (d + 1)) + R + K + 100) := by
  have he := Tournament.nodes_exact t
  have hN : N ≤ N * 2 ^ (d + 1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left N (Nat.one_le_two_pow (n := d + 1))
  unfold advance
  cases hwin : Tournament.winner t with
  | none =>
    dsimp only
    rw [he]
    have hpos : 1 ≤ d + 2 := by omega
    have hm := Nat.mul_le_mul_right (6 * (N * 2 ^ (d + 1)) + R + K + 100) hpos
    omega
  | some x =>
    have hb := replace_cells N (fun y : RowMerge.Front d α σ => key y.value) K
      (fun y => hk y.value) t x.row
      ((read x.after).1.1.map (fun z => (⟨x.row, z.1, z.2⟩ : RowMerge.Front d α σ)))
    have ha := hr x.after
    have hcoef : 4 * (N * 2 ^ (d + 1)) + K + 40 ≤
        6 * (N * 2 ^ (d + 1)) + R + K + 100 := by omega
    have hi := hb.trans (Nat.mul_le_mul_left (d + 1) hcoef)
    dsimp only
    rw [he]
    simp only [Nat.add_mul, Nat.one_mul] at hi ⊢
    omega

theorem advance_refines (N : ℕ) (key : α → ℤ × ℕ) (read : σ → Option (α × σ) × ℕ)
    (keyTrace : α → (ℤ × ℕ) × ℕ) (readTrace : σ → (Option (α × σ) × ℕ) × ℕ)
    (hk : ∀ x, (keyTrace x).1 = key x) (hr : ∀ s, (readTrace s).1 = read s) {d : ℕ}
    (t : Tournament.Tree (RowMerge.Front d α σ) d) :
    (advance N keyTrace readTrace t).1 = RowMerge.measuredAdvance key read t := by
  rw [advance_value]
  have hkey : (fun x => (keyTrace x).1) = key := funext hk
  have hread : (fun s => (readTrace s).1) = read := funext hr
  rw [hkey, hread]

def next (N : ℕ) (key : α → ℤ × ℕ) (read : σ → Option (α × σ) × ℕ)
    (keyTrace : α → (ℤ × ℕ) × ℕ) (readTrace : σ → (Option (α × σ) × ℕ) × ℕ)
    (hk : ∀ x, (keyTrace x).1 = key x) (hr : ∀ s, (readTrace s).1 = read s)
    (view : σ → List α) (hread : RowMerge.IsReader (fun s => (read s).1) view)
    {d : ℕ} (s : MergedReader.State (fun x => (key x).1) view d) :
    (Option (α × MergedReader.State (fun x => (key x).1) view d) × ℕ) × ℕ :=
  let q := advance N keyTrace readTrace s.tree
  have he : q.1 = RowMerge.measuredAdvance key read s.tree :=
    advance_refines N key read keyTrace readTrace hk hr s.tree
  match hq : q.1.1 with
  | none => ((none, q.1.2), q.2 + 8)
  | some (a, t) =>
    have ha : RowMerge.advance (fun x => (key x).1) (fun s => (read s).1) s.tree = some (a, t) :=
      (RowMerge.measuredAdvance_value key read s.tree).symm.trans
        ((congrArg Prod.fst he).symm.trans hq)
    ((some (a, ⟨t, RowMerge.advance_valid _ _ s.tree s.valid ha,
      RowMerge.advance_aligned _ _ s.tree s.aligned ha,
      MergedReader.advance_sorted _ _ view hread s ha⟩), q.1.2), q.2 + 8)

theorem next_value (N : ℕ) (key : α → ℤ × ℕ) (read : σ → Option (α × σ) × ℕ)
    (keyTrace : α → (ℤ × ℕ) × ℕ) (readTrace : σ → (Option (α × σ) × ℕ) × ℕ)
    (hk : ∀ x, (keyTrace x).1 = key x) (hr : ∀ s, (readTrace s).1 = read s)
    (view : σ → List α) (hread : RowMerge.IsReader (fun s => (read s).1) view)
    {d : ℕ} (s : MergedReader.State (fun x => (key x).1) view d) :
    (next N key read keyTrace readTrace hk hr view hread s).1 =
      MergedReader.measuredNext key read view hread s := by
  have he := advance_refines N key read keyTrace readTrace hk hr s.tree
  unfold next MergedReader.measuredNext
  dsimp only
  split
  · rename_i hq
    split
    · dsimp only
      apply Prod.ext
      · rfl
      · exact congrArg (fun z => z.2) he
    · rename_i a t hs
      have ho := congrArg Prod.fst he
      rw [hq, hs] at ho
      cases ho
  · rename_i a t hq
    split
    · rename_i hs
      have ho := congrArg Prod.fst he
      rw [hq, hs] at ho
      cases ho
    · rename_i b u hs
      have ho := congrArg Prod.fst he
      rw [hq, hs] at ho
      have hp := Option.some.inj ho
      cases hp
      dsimp only
      apply Prod.ext
      · rfl
      · exact congrArg (fun z => z.2) he

theorem next_cells (N : ℕ) (key : α → ℤ × ℕ) (read : σ → Option (α × σ) × ℕ)
    (keyTrace : α → (ℤ × ℕ) × ℕ) (readTrace : σ → (Option (α × σ) × ℕ) × ℕ)
    (hk : ∀ x, (keyTrace x).1 = key x) (hr : ∀ s, (readTrace s).1 = read s)
    (view : σ → List α) (hread : RowMerge.IsReader (fun s => (read s).1) view)
    {d : ℕ} (s : MergedReader.State (fun x => (key x).1) view d)
    (K R : ℕ) (hK : ∀ x, (keyTrace x).2 ≤ K) (hR : ∀ s, (readTrace s).2 ≤ R) :
    (next N key read keyTrace readTrace hk hr view hread s).2 ≤
      (d + 2) * (6 * (N * 2 ^ (d + 1)) + R + K + 100) + 8 := by
  have h := advance_cells N keyTrace readTrace K R hK hR s.tree
  unfold next
  dsimp only
  split <;> exact Nat.add_le_add_right h 8

end LowSpaceSubsetSum.MeasuredReaderCells

end OAI
