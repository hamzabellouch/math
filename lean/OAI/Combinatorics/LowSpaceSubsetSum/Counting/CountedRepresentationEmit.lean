import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedMaskChecks

namespace OAI

/-! # Executed validity, weight and mask construction for parent reports -/

namespace LowSpaceSubsetSum.CountedRepresentationEmit

variable {n : ℕ}

abbrev ParentRecord (n : ℕ) := (LeafRecord n × LeafRecord n) × (LeafRecord n × LeafRecord n)

def filterMask (selected : List (Fin n)) : List (Fin n) → List (Fin n) × ℕ
  | [] => ([], 1)
  | i :: xs =>
    let hit := CountedWeights.member i selected
    let rest := filterMask selected xs
    (if hit.1 then i :: rest.1 else rest.1, hit.2 + rest.2 + 3)

theorem filterMask_value (selected xs : List (Fin n)) :
    (filterMask selected xs).1 = xs.filter (fun i => decide (i ∈ selected)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [filterMask, CountedWeights.member_value, ih, List.filter_cons]

theorem filterMask_length (selected xs : List (Fin n)) :
    (filterMask selected xs).1.length ≤ xs.length := by
  rw [filterMask_value]
  exact List.length_filter_le _ _

theorem filterMask_work (selected xs : List (Fin n)) :
    (filterMask selected xs).2 ≤ (selected.length + 4) * xs.length + 1 := by
  induction xs with
  | nil => simp [filterMask]
  | cons i xs ih =>
    have h := CountedWeights.member_work i selected
    simp only [filterMask, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

def topIndices (x : ParentRecord n) : List (Fin n) :=
  x.1.1.top.indices ++ x.1.2.top.indices ++ x.2.1.top.indices ++ x.2.2.top.indices

theorem topIndices_length (x : ParentRecord n) : (topIndices x).length ≤ 4 * n := by
  have h₁ := x.1.1.top.length_le
  have h₂ := x.1.2.top.length_le
  have h₃ := x.2.1.top.length_le
  have h₄ := x.2.2.top.length_le
  simp only [topIndices, List.length_append]
  omega

def topMask (x : ParentRecord n) : IndexedMask n × ℕ :=
  let out := filterMask (topIndices x) (List.finRange n)
  (⟨out.1, by simpa only [List.length_finRange] using filterMask_length (topIndices x) (List.finRange n)⟩,
    out.2 + 12 * n + 4)

theorem topMask_value (x : ParentRecord n) :
    (topMask x).1.semantic = RepresentationUniverse.topMask
      (RepresentationKeys.pairSemantic x.1, RepresentationKeys.pairSemantic x.2) := by
  ext i
  simp [topMask, IndexedMask.semantic, filterMask_value, topIndices,
    RepresentationUniverse.topMask, RepresentationKeys.pairSemantic, LeafRecord.semantic]

theorem topMask_work (x : ParentRecord n) :
    (topMask x).2 ≤ 8 * (n + 1) ^ 2 := by
  have h := filterMask_work (topIndices x) (List.finRange n)
  have hl := topIndices_length x
  simp only [List.length_finRange] at h
  have hm := Nat.mul_le_mul_right n (Nat.add_le_add_right hl 4)
  change (filterMask (topIndices x) (List.finRange n)).2 + 12 * n + 4 ≤ _
  nlinarith only [h, hm, Nat.zero_le n]

def parentWeight (I : Instance n) (F : IndexedMask n) (x : ParentRecord n) : ℤ × ℕ :=
  let a := RepresentationKeys.leafWeight I F x.1.1
  let b := RepresentationKeys.leafWeight I F x.1.2
  let c := RepresentationKeys.leafWeight I F x.2.1
  let d := RepresentationKeys.leafWeight I F x.2.2
  ((a.1 + b.1) + (c.1 + d.1), a.2 + b.2 + c.2 + d.2 + 3)

theorem parentWeight_value (I : Instance n) (F : IndexedMask n) (x : ParentRecord n) :
    (parentWeight I F x).1 = RepresentationUniverse.parentWeight
      (flip (fun i => (I.values i : ℤ)) F.semantic)
      (RepresentationKeys.pairSemantic x.1, RepresentationKeys.pairSemantic x.2) := by
  simp only [parentWeight, RepresentationKeys.leafWeight_value,
    RepresentationUniverse.parentWeight, RepresentationUniverse.childWeight,
    RepresentationKeys.pairSemantic]

theorem parentWeight_work (I : Instance n) (F : IndexedMask n) (x : ParentRecord n) :
    (parentWeight I F x).2 ≤ 128 * (n + 1) ^ 2 + 3 := by
  have ha := RepresentationKeys.leafWeight_work I F x.1.1
  have hb := RepresentationKeys.leafWeight_work I F x.1.2
  have hc := RepresentationKeys.leafWeight_work I F x.2.1
  have hd := RepresentationKeys.leafWeight_work I F x.2.2
  change _ + _ + _ + _ + 3 ≤ _
  omega

def emit (I : Instance n) (F : IndexedMask n) (x y : LeafRecord n × LeafRecord n) :
    Option (StoredEntry n) × ℕ :=
  let checked := CountedMaskChecks.valid (x, y)
  if checked.1 then
    let w := parentWeight I F (x, y)
    let m := topMask (x, y)
    (some ⟨w.1, m.1⟩, checked.2 + w.2 + m.2 + 6)
  else (none, checked.2 + 3)

theorem emit_value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (x y : LeafRecord n × LeafRecord n) :
    (emit D.input F x y).1.map StoredEntry.semantic =
      D.emit (RepresentationKeys.pairSemantic x) (RepresentationKeys.pairSemantic y) := by
  simp only [emit, CountedMaskChecks.valid_value, decide_eq_true_eq,
    RepresentationParentData.emit]
  split
  · simp only [Option.map_some, StoredEntry.semantic, parentWeight_value, topMask_value, hF,
      RepresentationUniverse.entry, RepresentationParentData.weights]
  · rfl

theorem emit_work (I : Instance n) (F : IndexedMask n) (x y : LeafRecord n × LeafRecord n) :
    (emit I F x y).2 ≤ 500 * (n + 1) ^ 2 := by
  have hv := CountedMaskChecks.valid_work (x, y)
  have hw := parentWeight_work I F (x, y)
  have hm := topMask_work (x, y)
  simp only [emit]
  split <;> dsimp only <;> nlinarith only [hv, hw, hm, Nat.zero_le n]

theorem emit_scale (I : Instance n) (F : IndexedMask n) (x y : LeafRecord n × LeafRecord n)
    (hn : 10000 ≤ n) : (emit I F x y).2 ≤ inputScale I ^ 3 := by
  have h := emit_work I F x y
  have hnu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hu : 500 ≤ inputScale I := by omega
  calc
    _ ≤ 500 * (n + 1) ^ 2 := h
    _ ≤ 500 * inputScale I ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnu _)
    _ ≤ inputScale I * inputScale I ^ 2 := Nat.mul_le_mul_right _ hu
    _ = _ := (pow_succ' _ _).symm

end LowSpaceSubsetSum.CountedRepresentationEmit

end OAI
