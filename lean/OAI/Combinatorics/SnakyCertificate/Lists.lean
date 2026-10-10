import OAI.Combinatorics.SnakyCertificate.Rows

namespace OAI

namespace SnakyCertificate.Check

abbrev Key := ℤ ×ₗ ℤ

def mergeFuel : ℕ → List Cell → List Cell → List Cell
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | n + 1, x :: xs, y :: ys =>
    if x = y then x :: mergeFuel n xs ys
    else if toLex x < toLex y then x :: mergeFuel n xs (y :: ys)
    else y :: mergeFuel n (x :: xs) ys

theorem mem_mergeFuel (z : Cell) (n : ℕ) (xs ys : List Cell) :
    z ∈ mergeFuel n xs ys ↔ z ∈ xs ∨ z ∈ ys := by
  induction n generalizing xs ys with
  | zero => simp [mergeFuel]
  | succ n ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons y ys =>
        simp only [mergeFuel]
        split
        · rename_i h; subst y
          simp only [List.mem_cons, ih]
          tauto
        · split <;> simp only [List.mem_cons, ih] <;> tauto

def mergeUnion (xs ys : List Cell) : List Cell :=
  mergeFuel (xs.length + ys.length) xs ys

@[simp] theorem mem_mergeUnion (z : Cell) (xs ys : List Cell) :
    z ∈ mergeUnion xs ys ↔ z ∈ xs ∨ z ∈ ys :=
  mem_mergeFuel z _ xs ys

@[simp] theorem toFinset_mergeUnion (xs ys : List Cell) :
    (mergeUnion xs ys).toFinset = xs.toFinset ∪ ys.toFinset := by
  ext z; simp

structure ListRow where
  A : List Cell
  H : List Cell
  height : ℕ
  deriving DecidableEq

def denote (d : ListRow) : RowData := ⟨d.A.toFinset, d.H.toFinset, d.height⟩

def keyPlace (t : Term) (p : Cell) : Cell :=
  placement t.rotation t.shift p

def sortFuel : ℕ → List Cell → List Cell
  | 0, xs => xs
  | n + 1, xs =>
    if xs.length ≤ 1 then xs else
      mergeUnion (sortFuel n (xs.take (xs.length / 2)))
        (sortFuel n (xs.drop (xs.length / 2)))

theorem mem_sortFuel (z : Cell) (n : ℕ) (xs : List Cell) :
    z ∈ sortFuel n xs ↔ z ∈ xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    simp only [sortFuel]
    split
    · rfl
    · rw [mem_mergeUnion, ih, ih, ← List.mem_append, List.take_append_drop]

def sorted (xs : List Cell) : List Cell := sortFuel xs.length xs

def place (t : Term) (d : ListRow) : ListRow :=
  ⟨sorted (d.A.map (keyPlace t)), sorted (d.H.map (keyPlace t)), d.height⟩

def unions (xs : List (List Cell)) : List Cell := xs.foldr mergeUnion []

def common (xs : List (List Cell)) : List Cell :=
  match xs with
  | [] => []
  | x :: rest => rest.foldr (· ∩ ·) x

def fork (ds : List ListRow) : ListRow :=
  ⟨(mergeUnion (unions (ds.map ListRow.A)) (common (ds.map ListRow.H))).filter
      (fun p => decide (p ≠ origin)),
   mergeUnion [origin] (unions (ds.map ListRow.H)),
   1 + (ds.map ListRow.height).foldr max 0⟩

@[simp] theorem toFinset_sorted (xs : List Cell) : (sorted xs).toFinset = xs.toFinset := by
  ext z; simp [sorted, mem_sortFuel]

@[simp] theorem denote_place (t : Term) (d : ListRow) :
    denote (place t d) = placeRow t (denote d) := by
  have heq (xs : List Cell) :
      (sorted (xs.map (keyPlace t))).toFinset = xs.toFinset.image (placement t.rotation t.shift) := by
    ext z
    simp [keyPlace]
  simp only [denote, place, placeRow, heq]

@[simp] theorem toFinset_unions (xs : List (List Cell)) :
    (unions xs).toFinset = (xs.map List.toFinset).foldr (· ∪ ·) ∅ := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all [unions]

@[simp] theorem toFinset_inter_cell (xs ys : List Cell) :
    (xs ∩ ys).toFinset = xs.toFinset ∩ ys.toFinset := by
  ext p; simp

theorem toFinset_inters (xs : List (List Cell)) (a : List Cell) :
    (xs.foldr (· ∩ ·) a).toFinset = (xs.map List.toFinset).foldr (· ∩ ·) a.toFinset := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all only [List.foldr_cons, List.map_cons, toFinset_inter_cell]

@[simp] theorem toFinset_common (ds : List ListRow) :
    (common (ds.map ListRow.H)).toFinset = commonH (ds.map denote) := by
  cases ds with
  | nil => rfl
  | cons d ds => simp [common, commonH, toFinset_inters, Function.comp_def, denote]

theorem denote_fork (ds : List ListRow) : denote (fork ds) = forkRow (ds.map denote) := by
  have hA : (unions (ds.map ListRow.A)).toFinset = unionA (ds.map denote) := by
    simp [unionA, Function.comp_def, denote]
  have hH : (unions (ds.map ListRow.H)).toFinset = unionH (ds.map denote) := by
    simp [unionH, Function.comp_def, denote]
  have hf (xs : List Cell) :
      (xs.filter (fun p => decide (p ≠ origin))).toFinset = xs.toFinset.erase origin := by
    ext p; simp [and_comm]
  simp only [denote, fork, hf, toFinset_mergeUnion, hA, hH, toFinset_common,
    List.toFinset_cons, List.toFinset_nil]
  simp [forkRow, denote, Function.comp_def]

end SnakyCertificate.Check

end OAI
