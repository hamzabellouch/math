import OAI.Combinatorics.EditApproximation.Queries.QueryLocalBuffers
import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The initial-cone gather uses the unfiltered center list: a seed at a
center must be read before the eligibility test at that center is known. -/

namespace EditApproximation.BinaryFraction



@[simp] theorem queryInitialConeCentersWithWork_value {n : ℕ} (N P : ℕ) (hP : 0 < P)
    (A value : BinaryFraction) (q : TargetInterval n) :
    (queryInitialConeCentersWithWork N P A value q).1 =
      rawInitialConeCenters N P A.value ⌈value.value⌉₊ q := by
  have hg (b : ℕ) : (gridStateBoxWithWork n (seedGridSpacing b P) ⌈value.value⌉₊ q.lo q.hi).1 =
      localTargetStates n (seedGridSpacing b P) ⌈value.value⌉₊ q := by
    rw [gridStateBoxWithWork_value _ _ _ _ _ (by unfold seedGridSpacing; omega)]
    rfl
  have hguard (b : ℕ) : (initialScaleGuardWithWork ⌈value.value⌉₊ b A).1 =
      decide ((⌈value.value⌉₊ : ℚ) / (16 * A.value ^ 2) ≤ b ∧
        (b : ℚ) ≤ 4 * A.value * ⌈value.value⌉₊) :=
    Bool.eq_iff_iff.mpr (by simp only [initialScaleGuardWithWork_value, decide_eq_true_eq])
  simp only [queryInitialConeCentersWithWork, naturalCeilingWithWork_value,
    arithmeticFlatMapWithWork_value, filterWithWork_value, dyadicScalesWithWork_value,
    hguard, seedGridSpacingWithWork_value _ _ hP, hg,
    rawInitialConeCenters]



@[simp] theorem queryInitialSeedReadWithWork_value {n : ℕ} (value : BinaryFraction) (q : TargetInterval n)
    (keys : List (TargetInterval n)) (words : List BinaryFraction) (r : TargetInterval n) :
    bitWordValue (queryInitialSeedReadWithWork value q keys words r).1 =
      if r = q then ⌈value.value⌉₊ else ⌈finiteAnswerTable keys (words.map BinaryFraction.value) r⌉₊ := by
  unfold queryInitialSeedReadWithWork
  by_cases hr : r = q
  · rw [ite_eq_left ((queryIntervalEqualWithWork_value r q).mpr hr), ite_eq_left hr]
    exact naturalCeilingWithWork_value value
  · rw [ite_eq_right (fun h => hr ((queryIntervalEqualWithWork_value r q).mp h)), ite_eq_right hr]
    simp only [naturalCeilingWithWork_value, queryParentReadWithWork_value]

theorem cachedInitialProgramReadWithWork_value_only {α : Type*} (source target : List α)
    (N P F : ℕ) (hP : 0 < P) (A a : BinaryFraction)
    (read : TargetInterval target.length → List Bool × ℕ) (q : TargetInterval target.length) :
    (cachedInitialProgramReadWithWork source.length N P F A a read q).1.value =
      localInitialConeTable source target (fun r => bitWordValue (read r).1) N P F A.value a.value q := by
  let R := ∑ r : TargetInterval target.length, (read r).2
  have hR (r : TargetInterval target.length) : (read r).2 ≤ R :=
    Finset.single_le_sum (f := fun r : TargetInterval target.length => (read r).2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  rw [(cachedInitialProgramReadWithWork_eq_cost source.length N P F A a read q R hR).1]
  exact (cachedInitialProgramWithWork_value_width source target N P F A a _ q hP).1

end EditApproximation.BinaryFraction

end OAI
