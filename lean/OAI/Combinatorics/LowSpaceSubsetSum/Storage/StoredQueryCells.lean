import OAI.Combinatorics.LowSpaceSubsetSum.Separators.StoredSeparatorCheck

namespace OAI

/-! # Executed stored-mask query continuation cells

Membership and local-code recursion are instrumented below. The incidence
array is shared; each of the two subsequent binary searches is tail recursive
and carries only its array pointer, cut, counter and scalar endpoints.
-/

namespace LowSpaceSubsetSum.StoredQueryCells

variable {n g : ℕ}

def member (i : Fin n) : List (Fin n) → (Bool × ℕ) × ℕ
  | [] => ((false, 1), 2)
  | j :: xs =>
    if i = j then ((true, 1), 4)
    else
      let rest := member i xs
      ((rest.1.1, rest.1.2 + 1), rest.2 + 4)

theorem member_value (i : Fin n) (xs : List (Fin n)) :
    (member i xs).1 = CountedWeights.member i xs := by
  induction xs with
  | nil => rfl
  | cons j xs ih => simp only [member, CountedWeights.member]; split <;> simp_all only

theorem member_cells (i : Fin n) (xs : List (Fin n)) :
    (member i xs).2 ≤ 4 * (xs.length + 1) := by
  induction xs with
  | nil => simp [member]
  | cons j xs ih => simp only [member, List.length_cons]; split <;> dsimp only <;> omega

def code : (g : ℕ) → (Fin g → (Bool × ℕ) × ℕ) → (ℕ × ℕ) × ℕ
  | 0, _ => ((0, 1), 4)
  | g + 1, bits =>
    let first := bits 0
    let rest := code g (fun j => bits j.succ)
    (((if first.1.1 then 1 else 0) + 2 * rest.1.1, first.1.2 + rest.1.2 + 2 * g + 6),
      max first.2 (2 * g + 12 + rest.2))

theorem code_value (g : ℕ) (bits : Fin g → (Bool × ℕ) × ℕ) :
    (code g bits).1 = StoredSeparatorQueries.code g (fun j => (bits j).1) := by
  induction g with
  | zero => rfl
  | succ g ih => simp only [code, StoredSeparatorQueries.code, ih]

theorem code_cells (g H : ℕ) (bits : Fin g → (Bool × ℕ) × ℕ)
    (hb : ∀ j, (bits j).2 ≤ H) :
    (code g bits).2 ≤ (H + 16) * (g + 1) ^ 2 := by
  induction g with
  | zero => simp only [code]; nlinarith only [Nat.zero_le H]
  | succ g ih =>
    have hr := ih (fun j => bits j.succ) (fun j => hb j.succ)
    have hf := hb 0
    change max _ _ ≤ _
    apply max_le
    · nlinarith only [hf, Nat.zero_le H, Nat.zero_le (H * g), Nat.zero_le (H * g ^ 2)]
    · nlinarith only [hr, Nat.zero_le H, Nat.zero_le (H * g)]

def localCode (row : Vector (Fin n) g) (x : StoredEntry n) : (Fin (2 ^ g) × ℕ) × ℕ :=
  let out := code g (fun j => member row[j] x.mask.indices)
  ((⟨out.1.1, by
    rw [code_value]
    simp only [member_value]
    rw [StoredSeparatorQueries.code_value]
    exact (PaddedRows.index g (fun j => (CountedWeights.member row[j] x.mask.indices).1)).isLt⟩,
    out.1.2), out.2)

theorem localCode_value (row : Vector (Fin n) g) (x : StoredEntry n) :
    (localCode row x).1 = StoredSeparatorQueries.localCode row x := by
  have h : (code g (fun j => member row[j] x.mask.indices)).1 =
      StoredSeparatorQueries.code g (fun j => CountedWeights.member row[j] x.mask.indices) := by
    simpa only [member_value] using code_value g (fun j => member row[j] x.mask.indices)
  apply Prod.ext
  · apply Fin.ext
    change (code g (fun j => member row[j] x.mask.indices)).1.1 =
      (StoredSeparatorQueries.code g (fun j => CountedWeights.member row[j] x.mask.indices)).1
    exact congrArg Prod.fst h
  · change (code g (fun j => member row[j] x.mask.indices)).1.2 =
      (StoredSeparatorQueries.code g (fun j => CountedWeights.member row[j] x.mask.indices)).2
    exact congrArg Prod.snd h

theorem localCode_cells (row : Vector (Fin n) g) (x : StoredEntry n) :
    (localCode row x).2 ≤ (4 * (n + 1) + 16) * (g + 1) ^ 2 := by
  apply code_cells g (4 * (n + 1))
  intro j
  exact (member_cells row[j] x.mask.indices).trans
    (Nat.mul_le_mul_left 4 (Nat.add_le_add_right x.mask.length_le 1))

def lookup (row : Vector (Fin n) g) (x : StoredEntry n)
    (store : Array (Array ℕ)) (hs : store.size = 2 ^ g) : (Array ℕ × ℕ) × ℕ :=
  let c := localCode row x
  ((store[c.1.1.val]'(by rw [hs]; exact c.1.1.isLt), c.1.2 + 1), c.2 + 8)

theorem lookup_value (row : Vector (Fin n) g) (x : StoredEntry n)
    (store : Array (Array ℕ)) (hs : store.size = 2 ^ g) :
    (lookup row x store hs).1 = StoredSeparatorQueries.lookup row x store hs := by
  simp only [lookup, localCode_value, StoredSeparatorQueries.lookup]

/-- Binary search allocates no list; its tail-state and both saved scalar
cutoffs are covered by the additional 32 cells. -/
def query (row : Vector (Fin n) g) (x : StoredEntry n)
    (store : Array (Array ℕ)) (hs : store.size = 2 ^ g)
    (steps lo hi : ℕ) : (Bool × ℕ) × ℕ :=
  let a := lookup row x store hs
  let h := StoredSeparatorQueries.hit steps a.1.1 lo hi
  ((h.1, a.1.2 + h.2 + 2), a.2 + 32)

theorem query_value (row : Vector (Fin n) g) (x : StoredEntry n)
    (store : Array (Array ℕ)) (hs : store.size = 2 ^ g) (steps lo hi : ℕ) :
    (query row x store hs steps lo hi).1 =
      (let a := StoredSeparatorQueries.lookup row x store hs
       let h := StoredSeparatorQueries.hit steps a.1 lo hi
       (h.1, a.2 + h.2 + 2)) := by
  simp only [query, lookup_value]

theorem query_cells (row : Vector (Fin n) g) (x : StoredEntry n)
    (store : Array (Array ℕ)) (hs : store.size = 2 ^ g) (steps lo hi : ℕ) :
    (query row x store hs steps lo hi).2 ≤ (4 * (n + 1) + 16) * (g + 1) ^ 2 + 40 := by
  exact Nat.add_le_add_right (Nat.add_le_add_right (localCode_cells row x) 8) 32

end LowSpaceSubsetSum.StoredQueryCells

end OAI
