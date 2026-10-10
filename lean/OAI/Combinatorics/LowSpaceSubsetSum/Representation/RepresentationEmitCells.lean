import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationKeyCells
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedRepresentationEmit

namespace OAI

/-! # Scratch of the concrete validity-and-entry callback

All masks are bounded index lists. Membership, overlap tests, canonical top
mask construction and four signed weights have explicit work counters. Input masks remain shared throughout.
-/

namespace LowSpaceSubsetSum.RepresentationEmitCells

variable {n : ℕ}

def disjointAcc (A B : IndexedMask n) : List (Fin n) → (Bool × ℕ) × ℕ
  | [] => ((true, 1), 4)
  | i :: xs =>
    let a := RepresentationKeyCells.member i A.indices
    let b := RepresentationKeyCells.member i B.indices
    let rest := disjointAcc A B xs
    ((! (a.1.1 && b.1.1) && rest.1.1, a.1.2 + b.1.2 + rest.1.2 + 5),
      max a.2 (max (b.2 + 4) (rest.2 + 8)))

theorem disjointAcc_value (A B : IndexedMask n) (xs : List (Fin n)) :
    (disjointAcc A B xs).1 = CountedMaskChecks.disjointAcc A B xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [disjointAcc, CountedMaskChecks.disjointAcc, RepresentationKeyCells.member_value, ih]

theorem disjointAcc_cells (A B : IndexedMask n) (xs : List (Fin n)) :
    (disjointAcc A B xs).2 ≤ 8 * xs.length + 2 * n + 12 := by
  induction xs with
  | nil => simp only [disjointAcc, List.length_nil]; omega
  | cons i xs ih =>
    have ha := RepresentationKeyCells.member_cells i A.indices
    have hb := RepresentationKeyCells.member_cells i B.indices
    have hA := A.length_le
    have hB := B.length_le
    simp only [disjointAcc, List.length_cons]
    omega

def disjoint (A B : IndexedMask n) : (Bool × ℕ) × ℕ :=
  let out := disjointAcc A B (List.finRange n)
  (out.1, out.2 + 2 * n + 4)

theorem disjoint_value (A B : IndexedMask n) :
    (disjoint A B).1 = CountedMaskChecks.disjoint A B := disjointAcc_value _ _ _

theorem disjoint_cells (A B : IndexedMask n) : (disjoint A B).2 ≤ 12 * n + 16 := by
  have h := disjointAcc_cells A B (List.finRange n)
  simp only [List.length_finRange] at h
  change _ + 2 * n + 4 ≤ _
  omega

def four (A B C D : IndexedMask n) : (Bool × ℕ) × ℕ :=
  let ab := disjoint A B
  let ac := disjoint A C
  let bc := disjoint B C
  let ad := disjoint A D
  let bd := disjoint B D
  let cd := disjoint C D
  ((ab.1.1 && ac.1.1 && bc.1.1 && ad.1.1 && bd.1.1 && cd.1.1,
      ab.1.2 + ac.1.2 + bc.1.2 + ad.1.2 + bd.1.2 + cd.1.2 + 6),
    max ab.2 (max ac.2 (max bc.2 (max ad.2 (max bd.2 cd.2)))) + 24)

theorem four_value (A B C D : IndexedMask n) :
    (four A B C D).1 = CountedMaskChecks.four A B C D := by
  simp only [four, CountedMaskChecks.four, disjoint_value]

theorem four_cells (A B C D : IndexedMask n) : (four A B C D).2 ≤ 12 * n + 40 := by
  have h₁ := disjoint_cells A B
  have h₂ := disjoint_cells A C
  have h₃ := disjoint_cells B C
  have h₄ := disjoint_cells A D
  have h₅ := disjoint_cells B D
  have h₆ := disjoint_cells C D
  change max _ (max _ (max _ (max _ (max _ _)))) + 24 ≤ _
  omega

def valid (x : CountedRepresentationEmit.ParentRecord n) : (Bool × ℕ) × ℕ :=
  let top := four x.1.1.top x.1.2.top x.2.1.top x.2.2.top
  let loc := four x.1.1.localMask x.1.2.localMask x.2.1.localMask x.2.2.localMask
  let bg := four x.1.1.background x.1.2.background x.2.1.background x.2.2.background
  ((top.1.1 && loc.1.1 && bg.1.1, top.1.2 + loc.1.2 + bg.1.2 + 3),
    max top.2 (max loc.2 bg.2) + 12)

theorem valid_value (x : CountedRepresentationEmit.ParentRecord n) :
    (valid x).1 = CountedMaskChecks.valid x := by
  simp only [valid, CountedMaskChecks.valid, four_value]

theorem valid_cells (x : CountedRepresentationEmit.ParentRecord n) :
    (valid x).2 ≤ 12 * n + 52 := by
  have h₁ := four_cells x.1.1.top x.1.2.top x.2.1.top x.2.2.top
  have h₂ := four_cells x.1.1.localMask x.1.2.localMask x.2.1.localMask x.2.2.localMask
  have h₃ := four_cells x.1.1.background x.1.2.background x.2.1.background x.2.2.background
  change max _ (max _ _) + 12 ≤ _
  omega

def filterMask (selected : List (Fin n)) : List (Fin n) → (List (Fin n) × ℕ) × ℕ
  | [] => (([], 1), 4)
  | i :: xs =>
    let hit := RepresentationKeyCells.member i selected
    let rest := filterMask selected xs
    ((if hit.1.1 then i :: rest.1.1 else rest.1.1, hit.1.2 + rest.1.2 + 3),
      max (hit.2 + 4) (rest.2 + 4))

theorem filterMask_value (selected xs : List (Fin n)) :
    (filterMask selected xs).1 = CountedRepresentationEmit.filterMask selected xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [filterMask, CountedRepresentationEmit.filterMask, RepresentationKeyCells.member_value, ih]

theorem filterMask_cells (selected xs : List (Fin n)) :
    (filterMask selected xs).2 ≤ 4 * xs.length + 2 * selected.length + 8 := by
  induction xs with
  | nil => simp only [filterMask, List.length_nil]; omega
  | cons i xs ih =>
    have h := RepresentationKeyCells.member_cells i selected
    simp only [filterMask, List.length_cons]
    omega

def topMask (x : CountedRepresentationEmit.ParentRecord n) : (IndexedMask n × ℕ) × ℕ :=
  let out := filterMask (CountedRepresentationEmit.topIndices x) (List.finRange n)
  have hl : out.1.1.length ≤ n := by
    change (filterMask (CountedRepresentationEmit.topIndices x) (List.finRange n)).1.1.length ≤ n
    rw [filterMask_value]
    simpa only [List.length_finRange] using
      CountedRepresentationEmit.filterMask_length (CountedRepresentationEmit.topIndices x) (List.finRange n)
  ((⟨out.1.1, hl⟩, out.1.2 + 12 * n + 4), out.2 + 14 * n + 16)

private theorem mask_ext {x y : IndexedMask n} (h : x.indices = y.indices) : x = y := by
  cases x
  cases y
  cases h
  rfl

theorem topMask_value (x : CountedRepresentationEmit.ParentRecord n) :
    (topMask x).1 = CountedRepresentationEmit.topMask x := by
  apply Prod.ext
  · apply mask_ext
    exact congrArg Prod.fst (filterMask_value _ _)
  · change (filterMask (CountedRepresentationEmit.topIndices x) (List.finRange n)).1.2 +
      12 * n + 4 = (CountedRepresentationEmit.filterMask
        (CountedRepresentationEmit.topIndices x) (List.finRange n)).2 + 12 * n + 4
    exact congrArg (fun q : List (Fin n) × ℕ => q.2 + 12 * n + 4) (filterMask_value _ _)

theorem topMask_cells (x : CountedRepresentationEmit.ParentRecord n) :
    (topMask x).2 ≤ 26 * n + 24 := by
  have h := filterMask_cells (CountedRepresentationEmit.topIndices x) (List.finRange n)
  have hl := CountedRepresentationEmit.topIndices_length x
  simp only [List.length_finRange] at h
  change _ + 14 * n + 16 ≤ _
  omega

def parentWeight (I : Instance n) (F : IndexedMask n) (x : CountedRepresentationEmit.ParentRecord n) :
    (ℤ × ℕ) × ℕ :=
  let a := RepresentationKeyCells.leafWeight I F x.1.1
  let b := RepresentationKeyCells.leafWeight I F x.1.2
  let c := RepresentationKeyCells.leafWeight I F x.2.1
  let d := RepresentationKeyCells.leafWeight I F x.2.2
  (((a.1.1 + b.1.1) + (c.1.1 + d.1.1), a.1.2 + b.1.2 + c.1.2 + d.1.2 + 3),
    max a.2 (max b.2 (max c.2 d.2)) + 16)

theorem parentWeight_value (I : Instance n) (F : IndexedMask n)
    (x : CountedRepresentationEmit.ParentRecord n) :
    (parentWeight I F x).1 = CountedRepresentationEmit.parentWeight I F x := by
  simp only [parentWeight, CountedRepresentationEmit.parentWeight, RepresentationKeyCells.leafWeight_value]

theorem parentWeight_cells (I : Instance n) (F : IndexedMask n)
    (x : CountedRepresentationEmit.ParentRecord n) : (parentWeight I F x).2 ≤ 12 * n + 40 := by
  have h₁ := RepresentationKeyCells.leafWeight_cells I F x.1.1
  have h₂ := RepresentationKeyCells.leafWeight_cells I F x.1.2
  have h₃ := RepresentationKeyCells.leafWeight_cells I F x.2.1
  have h₄ := RepresentationKeyCells.leafWeight_cells I F x.2.2
  change max _ (max _ (max _ _)) + 16 ≤ _
  omega

def emit (I : Instance n) (F : IndexedMask n) (x y : LeafRecord n × LeafRecord n) :
    (Option (StoredEntry n) × ℕ) × ℕ :=
  let checked := valid (x, y)
  if checked.1.1 then
    let w := parentWeight I F (x, y)
    let m := topMask (x, y)
    ((some ⟨w.1.1, m.1.1⟩, checked.1.2 + w.1.2 + m.1.2 + 6),
      max checked.2 (max w.2 m.2) + 16)
  else ((none, checked.1.2 + 3), checked.2 + 8)

theorem emit_value (I : Instance n) (F : IndexedMask n) (x y : LeafRecord n × LeafRecord n) :
    (emit I F x y).1 = CountedRepresentationEmit.emit I F x y := by
  simp only [emit, CountedRepresentationEmit.emit, valid_value, parentWeight_value, topMask_value]
  split <;> rfl

theorem emit_cells (I : Instance n) (F : IndexedMask n) (x y : LeafRecord n × LeafRecord n) :
    (emit I F x y).2 ≤ 26 * n + 100 := by
  have hc := valid_cells (x, y)
  have hw := parentWeight_cells I F (x, y)
  have hm := topMask_cells (x, y)
  unfold emit
  dsimp only
  split <;> dsimp only <;> omega

end LowSpaceSubsetSum.RepresentationEmitCells

end OAI
