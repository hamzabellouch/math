import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredEntry

namespace OAI

/-! # Executed overlap tests on bounded index lists -/

namespace LowSpaceSubsetSum.CountedMaskChecks

variable {n : ℕ}

def disjointAcc (A B : IndexedMask n) : List (Fin n) → Bool × ℕ
  | [] => (true, 1)
  | i :: xs =>
    let a := CountedWeights.member i A.indices
    let b := CountedWeights.member i B.indices
    let rest := disjointAcc A B xs
    (!(a.1 && b.1) && rest.1, a.2 + b.2 + rest.2 + 5)

theorem disjointAcc_value (A B : IndexedMask n) (xs : List (Fin n)) :
    (disjointAcc A B xs).1 = true ↔
      ∀ i ∈ xs, ¬(i ∈ A.indices ∧ i ∈ B.indices) := by
  induction xs with
  | nil => simp [disjointAcc]
  | cons i xs ih =>
    by_cases ha : i ∈ A.indices <;> by_cases hb : i ∈ B.indices <;>
      simp [disjointAcc, CountedWeights.member_value, ha, hb, ih]

theorem disjointAcc_work (A B : IndexedMask n) (xs : List (Fin n)) :
    (disjointAcc A B xs).2 ≤ (2 * n + 7) * xs.length + 1 := by
  induction xs with
  | nil => simp [disjointAcc]
  | cons i xs ih =>
    have ha := CountedWeights.member_work i A.indices
    have hb := CountedWeights.member_work i B.indices
    have hA := A.length_le
    have hB := B.length_le
    simp only [disjointAcc, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

def disjoint (A B : IndexedMask n) : Bool × ℕ := disjointAcc A B (List.finRange n)

theorem disjoint_value (A B : IndexedMask n) :
    (disjoint A B).1 = decide (Disjoint A.semantic B.semantic) := by
  apply Bool.eq_iff_iff.mpr
  simp only [disjoint, disjointAcc_value, decide_eq_true_eq, List.mem_finRange,
    forall_true_left, Finset.disjoint_left, IndexedMask.semantic, List.mem_toFinset]
  simp only [not_and]

theorem disjoint_work (A B : IndexedMask n) :
    (disjoint A B).2 ≤ (2 * n + 7) * n + 1 := by
  simpa only [disjoint, List.length_finRange] using disjointAcc_work A B (List.finRange n)

def four (A B C D : IndexedMask n) : Bool × ℕ :=
  let ab := disjoint A B
  let ac := disjoint A C
  let bc := disjoint B C
  let ad := disjoint A D
  let bd := disjoint B D
  let cd := disjoint C D
  (ab.1 && ac.1 && bc.1 && ad.1 && bd.1 && cd.1,
    ab.2 + ac.2 + bc.2 + ad.2 + bd.2 + cd.2 + 6)

theorem four_value (A B C D : IndexedMask n) :
    (four A B C D).1 = true ↔
      RepresentationUniverse.DisjointFour A.semantic B.semantic C.semantic D.semantic := by
  simp only [four, disjoint_value, Bool.and_eq_true, decide_eq_true_eq,
    RepresentationUniverse.DisjointFour, Finset.disjoint_union_left]
  tauto

theorem four_work (A B C D : IndexedMask n) :
    (four A B C D).2 ≤ 6 * ((2 * n + 7) * n + 1) + 6 := by
  have hab := disjoint_work A B
  have hac := disjoint_work A C
  have hbc := disjoint_work B C
  have had := disjoint_work A D
  have hbd := disjoint_work B D
  have hcd := disjoint_work C D
  change _ + _ + _ + _ + _ + _ + 6 ≤ _
  omega

def valid (x : (LeafRecord n × LeafRecord n) × (LeafRecord n × LeafRecord n)) : Bool × ℕ :=
  let top := four x.1.1.top x.1.2.top x.2.1.top x.2.2.top
  let loc := four x.1.1.localMask x.1.2.localMask x.2.1.localMask x.2.2.localMask
  let bg := four x.1.1.background x.1.2.background x.2.1.background x.2.2.background
  (top.1 && loc.1 && bg.1, top.2 + loc.2 + bg.2 + 3)

theorem valid_value (x : (LeafRecord n × LeafRecord n) × (LeafRecord n × LeafRecord n)) :
    (valid x).1 = decide (RepresentationUniverse.Valid
      (RepresentationKeys.pairSemantic x.1, RepresentationKeys.pairSemantic x.2)) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [valid, four_value, Bool.and_eq_true,
    RepresentationUniverse.Valid, RepresentationKeys.pairSemantic, LeafRecord.semantic]
  tauto

theorem valid_work (x : (LeafRecord n × LeafRecord n) × (LeafRecord n × LeafRecord n)) :
    (valid x).2 ≤ 18 * ((2 * n + 7) * n + 1) + 21 := by
  have ht := four_work x.1.1.top x.1.2.top x.2.1.top x.2.2.top
  have hl := four_work x.1.1.localMask x.1.2.localMask x.2.1.localMask x.2.2.localMask
  have hb := four_work x.1.1.background x.1.2.background x.2.1.background x.2.2.background
  change _ + _ + _ + 3 ≤ _
  omega

end LowSpaceSubsetSum.CountedMaskChecks

end OAI
