import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationKeys

namespace OAI

/-! # Live scratch of the concrete stored-record key

The membership and signed-sum recursions count their live frames. Generated
index lists are released between weight calls; masks and input values remain
shared. The first projection preserves both the numerical value and work.
-/

namespace LowSpaceSubsetSum.RepresentationKeyCells

variable {n : ℕ}

def member (i : Fin n) : List (Fin n) → (Bool × ℕ) × ℕ
  | [] => ((false, 1), 4)
  | j :: xs =>
    if i = j then ((true, 1), 4) else
      let out := member i xs
      ((out.1.1, out.1.2 + 1), out.2 + 2)

theorem member_value (i : Fin n) (xs : List (Fin n)) :
    (member i xs).1 = CountedWeights.member i xs := by
  induction xs with
  | nil => rfl
  | cons j xs ih => simp only [member, CountedWeights.member]; split <;> simp only [ih]

theorem member_cells (i : Fin n) (xs : List (Fin n)) :
    (member i xs).2 ≤ 2 * xs.length + 4 := by
  induction xs with
  | nil => simp [member]
  | cons j xs ih => simp only [member, List.length_cons]; split <;> dsimp only <;> omega

def signedAt (I : Instance n) (F : IndexedMask n) (i : Fin n) : (ℤ × ℕ) × ℕ :=
  let hit := member i F.indices
  ((if hit.1.1 then -(I.values i : ℤ) else (I.values i : ℤ), hit.1.2 + 2), hit.2 + 4)

theorem signedAt_value (I : Instance n) (F : IndexedMask n) (i : Fin n) :
    (signedAt I F i).1 = RepresentationKeys.signedAt I F i := by
  simp only [signedAt, member_value, RepresentationKeys.signedAt]

theorem signedAt_cells (I : Instance n) (F : IndexedMask n) (i : Fin n) :
    (signedAt I F i).2 ≤ 2 * n + 8 := by
  have h := member_cells i F.indices
  have hf := F.length_le
  change (member i F.indices).2 + 4 ≤ _
  omega

def sumIndices (I : Instance n) (F M : IndexedMask n) : List (Fin n) → (ℤ × ℕ) × ℕ
  | [] => ((0, 1), 4)
  | i :: xs =>
    let selected := member i M.indices
    let term := signedAt I F i
    let rest := sumIndices I F M xs
    (((if selected.1.1 then term.1.1 else 0) + rest.1.1,
      selected.1.2 + term.1.2 + rest.1.2 + 3),
      max selected.2 (max (term.2 + 4) (rest.2 + 8)))

theorem sumIndices_value (I : Instance n) (F M : IndexedMask n) (xs : List (Fin n)) :
    (sumIndices I F M xs).1 = RepresentationKeys.sumIndices I F M xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [sumIndices, RepresentationKeys.sumIndices, member_value, signedAt_value, ih]

theorem sumIndices_cells (I : Instance n) (F M : IndexedMask n) (xs : List (Fin n)) :
    (sumIndices I F M xs).2 ≤ 8 * xs.length + 2 * n + 12 := by
  induction xs with
  | nil => simp [sumIndices]
  | cons i xs ih =>
    have hm := member_cells i M.indices
    have hM := M.length_le
    have ht := signedAt_cells I F i
    simp only [sumIndices, List.length_cons]
    omega

def weight (I : Instance n) (F M : IndexedMask n) : (ℤ × ℕ) × ℕ :=
  let out := sumIndices I F M (List.ofFn id)
  (out.1, out.2 + 2 * n + 4)

theorem weight_value (I : Instance n) (F M : IndexedMask n) :
    (weight I F M).1 = RepresentationKeys.weight I F M :=
  sumIndices_value I F M _

theorem weight_cells (I : Instance n) (F M : IndexedMask n) :
    (weight I F M).2 ≤ 12 * n + 16 := by
  have h := sumIndices_cells I F M (List.ofFn id)
  simp only [List.length_ofFn] at h
  change _ + 2 * n + 4 ≤ _
  omega

def leafWeight (I : Instance n) (F : IndexedMask n) (x : LeafRecord n) : (ℤ × ℕ) × ℕ :=
  let a := weight I F x.top
  let b := weight I F x.localMask
  let c := weight I F x.background
  ((a.1.1 + b.1.1 + c.1.1, a.1.2 + b.1.2 + c.1.2 + 2),
    max a.2 (max b.2 c.2) + 8)

theorem leafWeight_value (I : Instance n) (F : IndexedMask n) (x : LeafRecord n) :
    (leafWeight I F x).1 = RepresentationKeys.leafWeight I F x := by
  simp only [leafWeight, weight_value, RepresentationKeys.leafWeight]

theorem leafWeight_cells (I : Instance n) (F : IndexedMask n) (x : LeafRecord n) :
    (leafWeight I F x).2 ≤ 12 * n + 24 := by
  have ha := weight_cells I F x.top
  have hb := weight_cells I F x.localMask
  have hc := weight_cells I F x.background
  change max _ (max _ _) + 8 ≤ _
  omega

def pairKey (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (x : LeafRecord n × LeafRecord n) : (ℤ × ℕ) × ℕ :=
  let a := leafWeight I F x.1
  let b := leafWeight I F x.2
  let result := match mode with
    | .direct => ((a.1.1 + b.1.1) % P, a.1.2 + b.1.2 + 4)
    | .complementary t => ((t - a.1.1 - b.1.1) % P, a.1.2 + b.1.2 + 6)
  (result, max a.2 b.2 + 8)

theorem pairKey_value (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (x : LeafRecord n × LeafRecord n) :
    (pairKey I F P mode x).1 = RepresentationKeys.pairKey I F P mode x := by
  cases mode <;> simp only [pairKey, RepresentationKeys.pairKey, leafWeight_value]

theorem pairKey_cells (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (x : LeafRecord n × LeafRecord n) : (pairKey I F P mode x).2 ≤ 12 * n + 32 := by
  have ha := leafWeight_cells I F x.1
  have hb := leafWeight_cells I F x.2
  change max _ _ + 8 ≤ _
  omega

end LowSpaceSubsetSum.RepresentationKeyCells

end OAI
