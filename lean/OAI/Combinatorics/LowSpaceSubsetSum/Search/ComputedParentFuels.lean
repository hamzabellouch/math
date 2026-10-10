import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedBinomial
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLeafWork

namespace OAI

/-! # Computed and cached parent loop limits

Only domain scans, two multiplicative binomial loops, and a doubling loop
are run per leaf. No subset list is enumerated to obtain a loop limit.
-/

namespace LowSpaceSubsetSum.ComputedParentFuels

variable {n : ℕ}

private def lengthAcc {α : Type*} : List α → ℕ → ℕ → ℕ × ℕ
  | [], value, work => (value, work + 1)
  | _ :: xs, value, work => lengthAcc xs (value + 1) (work + 2)

private theorem lengthAcc_eq {α : Type*} (xs : List α) (value work : ℕ) :
    lengthAcc xs value work = (value + xs.length, work + 2 * xs.length + 1) := by
  induction xs generalizing value work with
  | nil => simp [lengthAcc]
  | cons x xs ih => simp only [lengthAcc, ih, List.length_cons]; congr 1 <;> omega

private def powerAcc : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, value, work => (value, work + 1)
  | k + 1, value, work => powerAcc k (2 * value) (work + 3)

private theorem powerAcc_eq (k value work : ℕ) :
    powerAcc k value work = (value * 2 ^ k, work + 3 * k + 1) := by
  induction k generalizing value work with
  | zero => simp [powerAcc]
  | succ k ih =>
    simp only [powerAcc, ih, pow_succ]
    congr 1 <;> ring

def leaf (L : RepresentationLeaf (Fin n)) : ℕ × ℕ :=
  let ts := RepresentationLeaf.domainSort L.top
  let ms := RepresentationLeaf.domainSort L.mixer
  let bs := RepresentationLeaf.domainSort L.background
  let nt := lengthAcc ts.1 0 0
  let nm := lengthAcc ms.1 0 0
  let nb := lengthAcc bs.1 0 0
  let a := CountedBinomial.run nt.1 L.topCount
  let b := CountedBinomial.run nm.1 L.localCount
  let c := powerAcc nb.1 1 0
  (a.value * b.value * c.1,
    ts.2 + ms.2 + bs.2 + nt.2 + nm.2 + nb.2 +
      8 * a.steps + 8 * b.steps + c.2 + 12)

theorem leaf_value (L : RepresentationLeaf (Fin n)) : (leaf L).1 = L.occurrences.card := by
  simp only [leaf, lengthAcc_eq, powerAcc_eq, Nat.zero_add, Nat.one_mul,
    RepresentationLeaf.domainSort_length, CountedBinomial.run_value,
    RepresentationLeaf.occurrences_card]

/-- Closed form for the leaf count and its charged scalar-loop work. -/
theorem leaf_formula (L : RepresentationLeaf (Fin n)) :
    leaf L =
      (L.top.card.choose L.topCount * L.mixer.card.choose L.localCount * 2^L.background.card,
        (RepresentationLeaf.domainSort L.top).2 + (RepresentationLeaf.domainSort L.mixer).2 +
        (RepresentationLeaf.domainSort L.background).2 + (2*L.top.card+1) +
        (2*L.mixer.card+1) + (2*L.background.card+1) +
        8*(CountedBinomial.run L.top.card L.topCount).steps +
        8*(CountedBinomial.run L.mixer.card L.localCount).steps +
        (3*L.background.card+1) + 12) := by
  simp only [leaf, lengthAcc_eq, powerAcc_eq, Nat.zero_add, Nat.one_mul,
    RepresentationLeaf.domainSort_length, CountedBinomial.run_value]

theorem leaf_work (L : RepresentationLeaf (Fin n)) : (leaf L).2 ≤ 100 * (n + 1) ^ 2 := by
  have ht := RepresentationLeaf.domainSort_work L.top
  have hm := RepresentationLeaf.domainSort_work L.mixer
  have hb := RepresentationLeaf.domainSort_work L.background
  have hct : L.top.card ≤ n := by simpa using Finset.card_le_univ L.top
  have hcm : L.mixer.card ≤ n := by simpa using Finset.card_le_univ L.mixer
  have hcb : L.background.card ≤ n := by simpa using Finset.card_le_univ L.background
  have ha := CountedBinomial.run_steps L.top.card L.topCount
  have hbb := CountedBinomial.run_steps L.mixer.card L.localCount
  simp only [leaf, lengthAcc_eq, powerAcc_eq, Nat.zero_add,
    RepresentationLeaf.domainSort_length]
  nlinarith only [ht, hm, hb, hct, hcm, hcb, ha, hbb, Nat.zero_le n]

theorem leaf_bound (L : RepresentationLeaf (Fin n)) : (leaf L).1 ≤ 2 ^ (3 * n) := by
  rw [leaf_value, RepresentationLeaf.occurrences_card]
  have ht : L.top.card.choose L.topCount ≤ 2 ^ n :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide)
      (by simpa using Finset.card_le_univ L.top))
  have hm : L.mixer.card.choose L.localCount ≤ 2 ^ n :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide)
      (by simpa using Finset.card_le_univ L.mixer))
  have hb : 2 ^ L.background.card ≤ 2 ^ n := Nat.pow_le_pow_right (by decide)
    (by simpa using Finset.card_le_univ L.background)
  calc
    _ ≤ (2 ^ n * 2 ^ n) * 2 ^ n := Nat.mul_le_mul (Nat.mul_le_mul ht hm) hb
    _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega

structure Values where
  first : ℕ
  second : ℕ
  control : ℕ

/-- The four scalar counts are retained long enough to form both limits. -/
def run (D : RepresentationParentData n) : Values × ℕ :=
  let a := leaf (D.leaves 0)
  let b := leaf (D.leaves 1)
  let c := leaf (D.leaves 2)
  let d := leaf (D.leaves 3)
  let f := a.1 * b.1
  let g := c.1 * d.1
  (⟨f, g, f + g + 1⟩, a.2 + b.2 + c.2 + d.2 + 7)

theorem run_restrict (D : RepresentationParentData n) (P : MaskRestriction n) :
    run {D with maskRestriction := P} = run D := rfl

theorem run_congr_leaves (D E : RepresentationParentData n) (h : D.leaves = E.leaves) :
    run D = run E := by
  simp only [run, h]

private theorem lengthBound_eq (D : RepresentationPairData n) :
    D.lengthBound = D.left.occurrences.card * D.right.occurrences.card := by
  simp only [RepresentationPairData.lengthBound, RepresentationLeaf.enumerate_length]

theorem first_value (D : RepresentationParentData n) :
    (run D).1.first = (D.pair 0).lengthBound := by
  simp only [run, leaf_value, lengthBound_eq, RepresentationParentData.pair]
  rfl

theorem second_value (D : RepresentationParentData n) :
    (run D).1.second = (D.pair 1).lengthBound := by
  simp only [run, leaf_value, lengthBound_eq, RepresentationParentData.pair]
  rfl

theorem control_value (D : RepresentationParentData n) :
    (run D).1.control = (D.pair 0).lengthBound + (D.pair 1).lengthBound + 1 := by
  change (run D).1.first + (run D).1.second + 1 = _
  rw [first_value, second_value]

theorem run_bounds (D : RepresentationParentData n) :
    (run D).1.first ≤ 2 ^ (6 * n) ∧ (run D).1.second ≤ 2 ^ (6 * n) ∧
      (run D).1.control ≤ 2 ^ (6 * n + 2) := by
  have h0 := Nat.mul_le_mul (leaf_bound (D.leaves 0)) (leaf_bound (D.leaves 1))
  have h1 := Nat.mul_le_mul (leaf_bound (D.leaves 2)) (leaf_bound (D.leaves 3))
  have he : 2 ^ (3 * n) * 2 ^ (3 * n) = 2 ^ (6 * n) := by
    rw [← pow_add]; congr 1; omega
  rw [he] at h0 h1
  have hp : 1 ≤ 2 ^ (6 * n) := Nat.one_le_two_pow
  dsimp only [run]
  rw [pow_add]
  norm_num
  exact ⟨h0, h1, by omega⟩

theorem run_work (D : RepresentationParentData n) :
    (run D).2 ≤ 512 * (n + 1) ^ 2 := by
  have h0 := leaf_work (D.leaves 0)
  have h1 := leaf_work (D.leaves 1)
  have h2 := leaf_work (D.leaves 2)
  have h3 := leaf_work (D.leaves 3)
  have hp : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  change _ + _ + _ + _ + 7 ≤ _
  omega

theorem run_scale (D : RepresentationParentData n) (hn : 10000 ≤ n) :
    (run D).2 ≤ inputScale D.input ^ 3 := by
  have hnu : n + 1 ≤ inputScale D.input := by unfold inputScale; omega
  have hs := Nat.pow_le_pow_left hnu 2
  have hm := Nat.mul_le_mul_right (inputScale D.input ^ 2)
    (show 512 ≤ inputScale D.input by omega)
  exact (run_work D).trans (by nlinarith only [hs, hm])

end LowSpaceSubsetSum.ComputedParentFuels

end OAI
