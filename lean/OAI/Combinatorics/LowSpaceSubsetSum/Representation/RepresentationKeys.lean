import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedWeights
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationWeightedReader

namespace OAI

/-! # Polynomial-cost representation keys on bounded stored masks

The lists below are the stored mask representation. Their intrinsic length
bound applies to every value of the type, independently of successful
sampling or membership in an enumerated universe. Finite sets occur only in
the semantic map. All signed membership tests are executed on stored lists.
-/

namespace LowSpaceSubsetSum

structure IndexedMask (n : ℕ) where
  indices : List (Fin n)
  length_le : indices.length ≤ n

namespace IndexedMask

variable {n : ℕ}

def semantic (M : IndexedMask n) : Finset (Fin n) := M.indices.toFinset

/-- A canonical representation for the semantic correspondence. Enumeration
can instead retain its already generated sublist, with no sorting step. -/
def ofFinset (S : Finset (Fin n)) : IndexedMask n :=
  ⟨S.sort (· ≤ ·), by simpa using Finset.card_le_univ S⟩

@[simp] theorem ofFinset_semantic (S : Finset (Fin n)) :
    (ofFinset S).semantic = S := by simp [ofFinset, semantic]

end IndexedMask

structure LeafRecord (n : ℕ) where
  top : IndexedMask n
  localMask : IndexedMask n
  background : IndexedMask n

namespace LeafRecord

variable {n : ℕ}

def semantic (x : LeafRecord n) : RepresentationLeaf.Occurrence (Fin n) :=
  ((x.top.semantic, x.localMask.semantic), x.background.semantic)

def ofOccurrence (x : RepresentationLeaf.Occurrence (Fin n)) : LeafRecord n :=
  ⟨IndexedMask.ofFinset x.1.1, IndexedMask.ofFinset x.1.2, IndexedMask.ofFinset x.2⟩

@[simp] theorem ofOccurrence_semantic (x : RepresentationLeaf.Occurrence (Fin n)) :
    (ofOccurrence x).semantic = x := by simp [ofOccurrence, semantic]

end LeafRecord

namespace RepresentationKeys

variable {n : ℕ}

/-- Indexed input lookup, one explicit sign membership test, and negation. -/
def signedAt (I : Instance n) (F : IndexedMask n) (i : Fin n) : ℤ × ℕ :=
  let hit := CountedWeights.member i F.indices
  (if hit.1 then -(I.values i : ℤ) else (I.values i : ℤ), hit.2 + 2)

theorem signedAt_value (I : Instance n) (F : IndexedMask n) (i : Fin n) :
    (signedAt I F i).1 = flip (fun i => (I.values i : ℤ)) F.semantic i := by
  simp only [signedAt, CountedWeights.member_value, IndexedMask.semantic,
    List.mem_toFinset, flip, decide_eq_true_eq]

theorem signedAt_work (I : Instance n) (F : IndexedMask n) (i : Fin n) :
    (signedAt I F i).2 ≤ n + 3 := by
  have h := CountedWeights.member_work i F.indices
  have hf := F.length_le
  change (CountedWeights.member i F.indices).2 + 2 ≤ _
  omega

/-- All input indices are visited; both membership and signed-input lookup
are charged even at indices outside the selected mask. -/
def sumIndices (I : Instance n) (F M : IndexedMask n) : List (Fin n) → ℤ × ℕ
  | [] => (0, 1)
  | i :: xs =>
    let selected := CountedWeights.member i M.indices
    let term := signedAt I F i
    let rest := sumIndices I F M xs
    ((if selected.1 then term.1 else 0) + rest.1,
      selected.2 + term.2 + rest.2 + 3)

theorem sumIndices_value (I : Instance n) (F M : IndexedMask n) (xs : List (Fin n)) :
    (sumIndices I F M xs).1 =
      (xs.map (fun i => if i ∈ M.semantic then
        flip (fun i => (I.values i : ℤ)) F.semantic i else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [sumIndices, CountedWeights.member_value, signedAt_value,
      IndexedMask.semantic, List.mem_toFinset, decide_eq_true_eq,
      List.map_cons, List.sum_cons, ih]

theorem sumIndices_work (I : Instance n) (F M : IndexedMask n) (xs : List (Fin n)) :
    (sumIndices I F M xs).2 ≤ (2 * n + 7) * xs.length + 1 := by
  induction xs with
  | nil => simp [sumIndices]
  | cons i xs ih =>
    have hm := CountedWeights.member_work i M.indices
    have ht := signedAt_work I F i
    have hM := M.length_le
    simp only [sumIndices, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

def weight (I : Instance n) (F M : IndexedMask n) : ℤ × ℕ :=
  sumIndices I F M (List.ofFn id)

theorem weight_value (I : Instance n) (F M : IndexedMask n) :
    (weight I F M).1 = LowSpaceSubsetSum.weight
      (flip (fun i => (I.values i : ℤ)) F.semantic) M.semantic := by
  rw [weight, sumIndices_value]
  simp only [List.map_ofFn, Function.comp_id, List.sum_ofFn, LowSpaceSubsetSum.weight]

theorem weight_work (I : Instance n) (F M : IndexedMask n) :
    (weight I F M).2 ≤ (2 * n + 7) * n + 1 := by
  simpa only [weight, List.length_ofFn] using sumIndices_work I F M (List.ofFn id)

def leafWeight (I : Instance n) (F : IndexedMask n) (x : LeafRecord n) : ℤ × ℕ :=
  let a := weight I F x.top
  let b := weight I F x.localMask
  let c := weight I F x.background
  (a.1 + b.1 + c.1, a.2 + b.2 + c.2 + 2)

theorem leafWeight_value (I : Instance n) (F : IndexedMask n) (x : LeafRecord n) :
    (leafWeight I F x).1 = RepresentationLeaf.occurrenceWeight
      (flip (fun i => (I.values i : ℤ)) F.semantic) x.semantic := by
  simp only [leafWeight, weight_value, LeafRecord.semantic, RepresentationLeaf.occurrenceWeight]

theorem leafWeight_work (I : Instance n) (F : IndexedMask n) (x : LeafRecord n) :
    (leafWeight I F x).2 ≤ 32 * (n + 1) ^ 2 := by
  have ha := weight_work I F x.top
  have hb := weight_work I F x.localMask
  have hc := weight_work I F x.background
  change _ + _ + _ + 2 ≤ _
  nlinarith only [ha, hb, hc, Nat.zero_le n]

def pairSemantic (x : LeafRecord n × LeafRecord n) :
    RepresentationUniverse.ChildOccurrence (Fin n) := (x.1.semantic, x.2.semantic)

/-- Both complete leaf weights and every modular operation are charged. -/
def pairKey (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (x : LeafRecord n × LeafRecord n) : ℤ × ℕ :=
  let a := leafWeight I F x.1
  let b := leafWeight I F x.2
  match mode with
  | .direct => ((a.1 + b.1) % P, a.2 + b.2 + 4)
  | .complementary t => ((t - a.1 - b.1) % P, a.2 + b.2 + 6)

theorem pairKey_value (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (x : LeafRecord n × LeafRecord n) :
    (pairKey I F P mode x).1 =
      FilteredStream.key
        (RepresentationLeaf.occurrenceWeight (flip (fun i => (I.values i : ℤ)) F.semantic))
        (RepresentationLeaf.occurrenceWeight (flip (fun i => (I.values i : ℤ)) F.semantic))
        P mode (pairSemantic x) := by
  cases mode <;> simp only [pairKey, pairSemantic, FilteredStream.key, leafWeight_value]

theorem pairKey_work (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (x : LeafRecord n × LeafRecord n) :
    (pairKey I F P mode x).2 ≤ 70 * (n + 1) ^ 2 := by
  have ha := leafWeight_work I F x.1
  have hb := leafWeight_work I F x.2
  have hpos : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  cases mode <;> change _ + _ + _ ≤ _ <;> omega

/-- Uniform bound for every representable key, with no record-membership
or successful-trial hypothesis. -/
theorem pairKey_scale (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (x : LeafRecord n × LeafRecord n)
    (hn : 10000 ≤ n) :
    (pairKey I F P mode x).2 ≤ inputScale I ^ 3 := by
  have h := pairKey_work I F P mode x
  have hnU : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hu : 70 ≤ inputScale I := by omega
  have hs := Nat.pow_le_pow_left hnU 2
  have hm := Nat.mul_le_mul_right (inputScale I ^ 2) hu
  nlinarith only [h, hs, hm]

/-- The parent key is recovered by the semantic mask map. The sign
representation is fixed once before any reader is created. -/
theorem parent_pairKey_value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) (x : LeafRecord n × LeafRecord n) :
    (pairKey D.input F D.modulus (D.pair j).mode x).1 = D.key j (pairSemantic x) := by
  rw [pairKey_value, hF]
  rfl

private theorem stored_reader (right : Array (LeafRecord n)) :
    RowMerge.IsReader (fun s => (FilteredStream.countedRead right s).1)
      (FilteredStream.view (α := LeafRecord n) right) := by
  simpa only [FilteredStream.countedRead_value] using
    (FilteredStream.reader (α := LeafRecord n) right)

/-- All internal tournament keys use the concrete list-mask evaluator. -/
def read (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ}
    (s : MergedReader.State (fun x => (pairKey I F P mode x).1)
      (FilteredStream.view right) d) :=
  MergedReader.measuredNext (pairKey I F P mode) (FilteredStream.countedRead right)
    (FilteredStream.view right) (stored_reader right) s

theorem read_value (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (right : Array (LeafRecord n)) {d : ℕ}
    (s : MergedReader.State (fun x => (pairKey I F P mode x).1)
      (FilteredStream.view right) d) :
    (read I F P mode right s).1 =
      MergedReader.next (fun x => (pairKey I F P mode x).1)
        (fun s => (FilteredStream.countedRead right s).1)
        (FilteredStream.view right) (stored_reader right) s :=
  MergedReader.measuredNext_value _ _ _ _ _

theorem read_work (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (right : Array (LeafRecord n)) {d : ℕ}
    (s : MergedReader.State (fun x => (pairKey I F P mode x).1)
      (FilteredStream.view right) d) (hd : d ≤ n) (hn : 10000 ≤ n) :
    (read I F P mode right s).2 ≤ (2 * inputScale I ^ 3 + 8) * n + 34 := by
  have h := MergedReader.measuredNext_work (pairKey I F P mode)
    (FilteredStream.countedRead right) (FilteredStream.view right) (stored_reader right) s
    (inputScale I ^ 3) 24 (fun x => pairKey_scale I F P mode x hn)
    (FilteredStream.countedRead_work right)
  change (read I F P mode right s).2 ≤ _ at h
  have hm := Nat.mul_le_mul_left (2 * inputScale I ^ 3 + 8) hd
  omega

private theorem read_polynomial {n u : ℕ} (hnu : n ≤ u) (hu : 10000 ≤ u) :
    (2 * u ^ 3 + 8) * n + 34 ≤ u ^ 5 := by
  have hu3 : 8 ≤ u ^ 3 := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ u ^ 3 := Nat.pow_le_pow_left (by omega) _
  have hu4 : 34 ≤ u ^ 4 := by
    calc
      34 ≤ 3 ^ 4 := by norm_num
      _ ≤ u ^ 4 := Nat.pow_le_pow_left (by omega) _
  have hcoef : 2 * u ^ 3 + 8 ≤ 3 * u ^ 3 := by omega
  have hm : (2 * u ^ 3 + 8) * n ≤ 3 * u ^ 4 := by
    calc
      _ ≤ (3 * u ^ 3) * u := Nat.mul_le_mul hcoef hnu
      _ = _ := by ring
  have ht : 4 * u ^ 4 ≤ u ^ 5 := by
    calc
      _ ≤ u * u ^ 4 := Nat.mul_le_mul_right _ (by omega : 4 ≤ u)
      _ = _ := (pow_succ' u 4).symm
  omega

theorem read_scale (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (right : Array (LeafRecord n)) {d : ℕ}
    (s : MergedReader.State (fun x => (pairKey I F P mode x).1)
      (FilteredStream.view right) d) (hd : d ≤ n) (hn : 10000 ≤ n) :
    (read I F P mode right s).2 ≤ inputScale I ^ 5 := by
  have hnu : n ≤ inputScale I := by unfold inputScale; omega
  exact (read_work I F P mode right s hd hn).trans (read_polynomial hnu (hn.trans hnu))

end RepresentationKeys
end LowSpaceSubsetSum

end OAI
