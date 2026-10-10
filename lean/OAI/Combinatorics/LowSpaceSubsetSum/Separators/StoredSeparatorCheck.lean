import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredEntryTerminal
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.StoredSeparatorQueries
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.StoredIncidenceBuild
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.MeasuredSeparatorTraversal
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorExecutionMap

namespace OAI

/-! # A measured separator checker on stored dictionaries

Each block retains its coordinate vector and both incidence tables. The
recursive checker passes those fixed tables to the measured DFS; only
record-pointer lists are filtered or sorted during individual checks.
-/

namespace LowSpaceSubsetSum.StoredSeparatorCheck

variable {n g : ℕ}

structure Block (n g : ℕ) where
  row : Vector (Fin n) g
  familySize : ℕ
  depth : ℕ
  steps : ℕ
  leftStore : Array (Array ℕ)
  rightStore : Array (Array ℕ)
  leftSize : leftStore.size = 2 ^ g
  rightSize : rightStore.size = 2 ^ g
  depth_eq : depth = Nat.clog 2 familySize
  leftSorted : ∀ i : Fin leftStore.size,
    Monotone (fun j : Fin leftStore[i.val].size => leftStore[i.val][j.val])
  rightSorted : ∀ i : Fin rightStore.size,
    Monotone (fun j : Fin rightStore[i.val].size => rightStore[i.val][j.val])
  leftBound : ∀ i : Fin leftStore.size, leftStore[i.val].size < 2 ^ steps
  rightBound : ∀ i : Fin rightStore.size, rightStore[i.val].size < 2 ^ steps

namespace Block

def left (b : Block n g) (x : StoredEntry n) : Array ℕ :=
  (StoredSeparatorQueries.lookup b.row x b.leftStore b.leftSize).1

def right (b : Block n g) (x : StoredEntry n) : Array ℕ :=
  (StoredSeparatorQueries.lookup b.row x b.rightStore b.rightSize).1

private theorem left_sorted (b : Block n g) (x : StoredEntry n) :
    Monotone (fun j : Fin (b.left x).size => (b.left x)[j.val]) := by
  exact b.leftSorted ⟨(StoredSeparatorQueries.localCode b.row x).1.val,
    by rw [b.leftSize]; exact (StoredSeparatorQueries.localCode b.row x).1.isLt⟩

private theorem right_sorted (b : Block n g) (x : StoredEntry n) :
    Monotone (fun j : Fin (b.right x).size => (b.right x)[j.val]) := by
  exact b.rightSorted ⟨(StoredSeparatorQueries.localCode b.row x).1.val,
    by rw [b.rightSize]; exact (StoredSeparatorQueries.localCode b.row x).1.isLt⟩

private theorem left_bound (b : Block n g) (x : StoredEntry n) :
    (b.left x).size < 2 ^ b.steps := by
  exact b.leftBound ⟨(StoredSeparatorQueries.localCode b.row x).1.val,
    by rw [b.leftSize]; exact (StoredSeparatorQueries.localCode b.row x).1.isLt⟩

private theorem right_bound (b : Block n g) (x : StoredEntry n) :
    (b.right x).size < 2 ^ b.steps := by
  exact b.rightBound ⟨(StoredSeparatorQueries.localCode b.row x).1.val,
    by rw [b.rightSize]; exact (StoredSeparatorQueries.localCode b.row x).1.isLt⟩

def source (b : Block n g) : SeparatorBlocks.Block (StoredEntry n) (StoredEntry n) where
  size := b.familySize
  left := b.left
  right := b.right
  left_sorted := b.left_sorted
  right_sorted := b.right_sorted

def leftQuery (b : Block n g) (x : StoredEntry n) (lo hi : ℕ) : Bool × ℕ :=
  let a := StoredSeparatorQueries.lookup b.row x b.leftStore b.leftSize
  let h := StoredSeparatorQueries.hit b.steps a.1 lo hi
  (h.1, a.2 + h.2 + 2)

def rightQuery (b : Block n g) (x : StoredEntry n) (lo hi : ℕ) : Bool × ℕ :=
  let a := StoredSeparatorQueries.lookup b.row x b.rightStore b.rightSize
  let h := StoredSeparatorQueries.hit b.steps a.1 lo hi
  (h.1, a.2 + h.2 + 2)

theorem leftQuery_value (b : Block n g) (x : StoredEntry n) (lo hi : ℕ) :
    (b.leftQuery x lo hi).1 = SeparatorIncidenceTable.hit (b.left x) lo hi :=
  StoredSeparatorQueries.hit_value b.steps _ (b.left_sorted x) (b.left_bound x) lo hi

theorem rightQuery_value (b : Block n g) (x : StoredEntry n) (lo hi : ℕ) :
    (b.rightQuery x lo hi).1 = SeparatorIncidenceTable.hit (b.right x) lo hi :=
  StoredSeparatorQueries.hit_value b.steps _ (b.right_sorted x) (b.right_bound x) lo hi

def queryBound (b : Block n g) : ℕ := (n + 7) * (g + 1) ^ 2 + 20 * b.steps + 6

theorem leftQuery_work (b : Block n g) (x : StoredEntry n) (lo hi : ℕ) :
    (b.leftQuery x lo hi).2 ≤ b.queryBound := by
  have hl := StoredSeparatorQueries.lookup_work b.row x b.leftStore b.leftSize
  have hh := StoredSeparatorQueries.hit_work b.steps (b.left x) lo hi
  dsimp only [left] at hh
  change _ + _ + 2 ≤ _
  unfold queryBound
  omega

theorem rightQuery_work (b : Block n g) (x : StoredEntry n) (lo hi : ℕ) :
    (b.rightQuery x lo hi).2 ≤ b.queryBound := by
  have hl := StoredSeparatorQueries.lookup_work b.row x b.rightStore b.rightSize
  have hh := StoredSeparatorQueries.hit_work b.steps (b.right x) lo hi
  dsimp only [right] at hh
  change _ + _ + 2 ≤ _
  unfold queryBound
  omega

end Block

private theorem preprocess_sorted
    (test : Fin (2 ^ g) → Fin (2 ^ g) → Bool × ℕ)
    (family : Array (Fin (2 ^ g)))
    (i : Fin (StoredIncidenceBuild.preprocess test family).1.size) :
    Monotone (fun j : Fin (StoredIncidenceBuild.preprocess test family).1[i.val].size =>
      (StoredIncidenceBuild.preprocess test family).1[i.val][j.val]) := by
  have hi : i.val < 2 ^ g := by
    simpa only [StoredIncidenceBuild.preprocess_size] using i.isLt
  have he := StoredIncidenceBuild.preprocess_get test family ⟨i.val, hi⟩
  exact SeparatorBlocks.transport_sorted _ _ he.symm
    (SeparatorIncidenceTable.table_monotone _ _ _)

private theorem preprocess_bound
    (test : Fin (2 ^ g) → Fin (2 ^ g) → Bool × ℕ)
    (family : Array (Fin (2 ^ g))) (steps : ℕ) (hs : family.size < 2 ^ steps)
    (i : Fin (StoredIncidenceBuild.preprocess test family).1.size) :
    (StoredIncidenceBuild.preprocess test family).1[i.val].size < 2 ^ steps := by
  have hi : i.val < 2 ^ g := by
    simpa only [StoredIncidenceBuild.preprocess_size] using i.isLt
  have he := congrArg Array.size (StoredIncidenceBuild.preprocess_get test family ⟨i.val, hi⟩)
  exact he.trans_lt ((SeparatorIncidenceTable.table_length _ _ _).trans_lt hs)

/-- The table construction runs once for this block. -/
def prepareBlock (row : Vector (Fin n) g) (family : Array (Fin (2 ^ g)))
    (depth steps : ℕ) (hd : depth = Nat.clog 2 family.size)
    (hs : family.size < 2 ^ steps) : Block n g × ℕ :=
  let t := StoredIncidenceBuild.tables family
  ({ row := row, familySize := family.size, depth := depth, steps := steps
     leftStore := t.1.1, rightStore := t.1.2
     leftSize := StoredIncidenceBuild.preprocess_size _ _
     rightSize := StoredIncidenceBuild.preprocess_size _ _
     depth_eq := hd
     leftSorted := fun i => preprocess_sorted StoredIncidenceBuild.contains family i
     rightSorted := fun i => preprocess_sorted StoredIncidenceBuild.avoids family i
     leftBound := fun i => preprocess_bound StoredIncidenceBuild.contains family steps hs i
     rightBound := fun i => preprocess_bound StoredIncidenceBuild.avoids family steps hs i }, t.2 + 12)

theorem prepareBlock_work (row : Vector (Fin n) g) (family : Array (Fin (2 ^ g)))
    (depth steps : ℕ) (hd : depth = Nat.clog 2 family.size)
    (hs : family.size < 2 ^ steps) (hsize : family.size ≤ 11 * 2 ^ g) :
    (prepareBlock row family depth steps hd hs).2 ≤ 220 * 2 ^ (2 * g) + 12 :=
  Nat.add_le_add_right (StoredIncidenceBuild.tables_work_of_size family hsize) 12

/-- Four preparations are shared by every dictionary check in this trial. -/
def prepareFour (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g))) (depths steps : Fin 4 → ℕ)
    (hd : ∀ i, depths i = Nat.clog 2 (families i).size)
    (hs : ∀ i, (families i).size < 2 ^ steps i) : List (Block n g) × ℕ :=
  let a := prepareBlock (rows 0) (families 0) (depths 0) (steps 0) (hd 0) (hs 0)
  let b := prepareBlock (rows 1) (families 1) (depths 1) (steps 1) (hd 1) (hs 1)
  let c := prepareBlock (rows 2) (families 2) (depths 2) (steps 2) (hd 2) (hs 2)
  let d := prepareBlock (rows 3) (families 3) (depths 3) (steps 3) (hd 3) (hs 3)
  ([a.1, b.1, c.1, d.1], a.2 + b.2 + c.2 + d.2 + 5)

theorem prepareFour_value (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g))) (depths steps : Fin 4 → ℕ)
    (hd : ∀ i, depths i = Nat.clog 2 (families i).size)
    (hs : ∀ i, (families i).size < 2 ^ steps i) :
    (prepareFour rows families depths steps hd hs).1 = List.ofFn
      (fun i => (prepareBlock (rows i) (families i) (depths i) (steps i) (hd i) (hs i)).1) := rfl

theorem prepareFour_length (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g))) (depths steps : Fin 4 → ℕ)
    (hd : ∀ i, depths i = Nat.clog 2 (families i).size)
    (hs : ∀ i, (families i).size < 2 ^ steps i) :
    (prepareFour rows families depths steps hd hs).1.length = 4 := rfl

theorem prepareFour_work (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g))) (depths steps : Fin 4 → ℕ)
    (hd : ∀ i, depths i = Nat.clog 2 (families i).size)
    (hs : ∀ i, (families i).size < 2 ^ steps i)
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (prepareFour rows families depths steps hd hs).2 ≤ 880 * 2 ^ (2 * g) + 53 := by
  have h₀ := prepareBlock_work (rows 0) (families 0) (depths 0) (steps 0) (hd 0) (hs 0) (hsize 0)
  have h₁ := prepareBlock_work (rows 1) (families 1) (depths 1) (steps 1) (hd 1) (hs 1) (hsize 1)
  have h₂ := prepareBlock_work (rows 2) (families 2) (depths 2) (steps 2) (hd 2) (hs 2) (hsize 2)
  have h₃ := prepareBlock_work (rows 3) (families 3) (depths 3) (steps 3) (hd 3) (hs 3) (hsize 3)
  change _ + _ + _ + _ + 5 ≤ _
  omega

/-- The capacity is supplied once; guards charge their two list-length scans. -/
def run (capacity : ℕ) (target : ℤ) : List (Block n g) →
    List (StoredEntry n) → List (StoredEntry n) → Bool × ℕ
  | [], xs, ys =>
    let size := xs.length + ys.length
    if size ≤ capacity then
      let out := StoredEntryTerminal.run target xs ys
      (out.1, out.2 + 2 * size + 5)
    else (false, 2 * size + 3)
  | b :: rest, xs, ys =>
    let size := xs.length + ys.length
    if size ≤ capacity then
      let out := MeasuredSeparatorTraversal.run b.leftQuery b.rightQuery
        (fun _ => run capacity target rest) b.depth 0 b.familySize xs ys
      (out.1, out.2 + 2 * size + 5)
    else (false, 2 * size + 3)

theorem run_value (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (blocks : List (Block n g)) (xs ys : List (StoredEntry n)) :
    (run capacity target blocks xs ys).1 =
      (SeparatorBlocks.check n StoredEntry.value StoredEntry.value target
        (blocks.map Block.source) xs ys).accepted := by
  subst capacity
  induction blocks generalizing xs ys with
  | nil =>
    simp only [run, List.map_nil, SeparatorBlocks.check, SeparatorTerminal.bounded]
    split
    · rename_i hs
      exact StoredEntryTerminal.run_value target xs ys (by omega) (by omega)
    · rfl
  | cons b rest ih =>
    simp only [run, List.map_cons, SeparatorBlocks.check]
    split
    · have h := MeasuredSeparatorTraversal.run_value b.leftQuery b.rightQuery b.left b.right
        b.leftQuery_value b.rightQuery_value (fun _ => run (2 ^ n) target rest)
        (fun _ => SeparatorBlocks.check n StoredEntry.value StoredEntry.value target
          (rest.map Block.source)) (fun _ as bs => ih as bs) b.depth 0 b.familySize xs ys
      rw [h, b.depth_eq]
      rfl
    · rfl

def factor (n : ℕ) : List (Block n g) → ℕ
  | [] => 64 * (n + 1) + 5
  | b :: rest => 2 * b.queryBound + 2 * factor n rest + 37

private theorem factor_ge (blocks : List (Block n g)) : 5 ≤ factor n blocks := by
  cases blocks <;> simp only [factor] <;> omega

/-- Source scans are the same ledger used by the established expectation bound. -/
theorem run_work (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (blocks : List (Block n g)) (xs ys : List (StoredEntry n)) :
    (run capacity target blocks xs ys).2 ≤ factor n blocks *
      ((SeparatorBlocks.check n StoredEntry.value StoredEntry.value target
        (blocks.map Block.source) xs ys).scans + xs.length + ys.length + 1) := by
  subst capacity
  induction blocks generalizing xs ys with
  | nil =>
    have ht := StoredEntryTerminal.run_work target xs ys
    simp only [run, List.map_nil, SeparatorBlocks.check, SeparatorTerminal.bounded, factor]
    split
    · nlinarith only [ht, Nat.zero_le
        (SeparatorTerminal.run StoredEntry.value StoredEntry.value target xs ys).scans,
        Nat.zero_le n, Nat.zero_le xs.length, Nat.zero_le ys.length]
    · dsimp only
      nlinarith only [Nat.zero_le n, Nat.zero_le xs.length, Nat.zero_le ys.length]
  | cons b rest ih =>
    have hfac := factor_ge rest
    simp only [run, List.map_cons, SeparatorBlocks.check]
    split
    · have h := MeasuredSeparatorTraversal.run_work b.leftQuery b.rightQuery b.left b.right
        b.leftQuery_value b.rightQuery_value b.queryBound (factor n rest)
        b.leftQuery_work b.rightQuery_work (fun _ => run (2 ^ n) target rest)
        (fun _ => SeparatorBlocks.check n StoredEntry.value StoredEntry.value target
          (rest.map Block.source)) (fun _ as bs => ih as bs) b.depth 0 b.familySize xs ys
      rw [b.depth_eq] at h
      change _ + 2 * (xs.length + ys.length) + 5 ≤ _
      simp only [factor, Block.source, SeparatorBlocks.depth] at h ⊢
      rw [b.depth_eq]
      nlinarith only [h, hfac, Nat.zero_le xs.length, Nat.zero_le ys.length,
        Nat.zero_le ((2 * b.queryBound + 2 * factor n rest + 32) *
          (xs.length + ys.length))]
    · dsimp only
      have hf := factor_ge (b :: rest)
      nlinarith only [hf, Nat.zero_le xs.length, Nat.zero_le ys.length]

private theorem factor_add_bound (blocks : List (Block n g)) (Q : ℕ)
    (hQ : ∀ b ∈ blocks, b.queryBound ≤ Q) :
    factor n blocks + (2 * Q + 37) ≤
      2 ^ blocks.length * (64 * (n + 1) + 5 + (2 * Q + 37)) := by
  induction blocks with
  | nil => simp [factor]
  | cons b rest ih =>
    have hb := hQ b (by simp)
    have hr := ih (fun c hc => hQ c (by simp [hc]))
    simp only [factor, List.length_cons, pow_succ]
    nlinarith only [hb, hr]

theorem four_factor (blocks : List (Block n g)) (Q : ℕ)
    (hlen : blocks.length = 4) (hQ : ∀ b ∈ blocks, b.queryBound ≤ Q) :
    factor n blocks ≤ 16 * (64 * (n + 1) + 2 * Q + 42) := by
  have h := factor_add_bound blocks Q hQ
  rw [hlen] at h
  norm_num at h
  omega

end LowSpaceSubsetSum.StoredSeparatorCheck

end OAI
