import OAI.Analysis.OInfinity.NegativeCompletion
import OAI.Analysis.OInfinity.BinaryLeafRows

namespace OAI

/-! # Binary encoding of each finite stabilized canonical row

Two consecutive explicit range completions define a shift from each
prescribed generator to the next. Together with the first generator this
is a coisometric binary pair. No general even-row comparison is used.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

private def skipSecond (m : ℕ) : Fin (m + 1) → Fin (m + 2) :=
  Fin.cases 0 (fun i => i.succ.succ)

private lemma skipSecond_injective (m : ℕ) : Function.Injective (skipSecond m) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i <;> intro j <;> refine Fin.cases ?_ (fun j => ?_) j
  · intro _; rfl
  · intro h
    have hh := congrArg Fin.val h
    change 0 = (j : ℕ) + 1 + 1 at hh
    omega
  · intro h
    have hh := congrArg Fin.val h
    change (i : ℕ) + 1 + 1 = 0 at hh
    omega
  · intro h
    change i.succ.succ = j.succ.succ at h
    exact congrArg Fin.succ (Fin.succ_injective _ (Fin.succ_injective _ h))

private lemma skipSecond_ne_one (m : ℕ) (i : Fin (m + 1)) :
    skipSecond m i ≠ 1 := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact Fin.zero_ne_one
  · intro h
    have hh := congrArg Fin.val h
    change (i : ℕ) + 1 + 1 = 1 at hh
    omega

/-- Removing the second range of a full row leaves a shift isometry whose
complement is exactly that second range. -/
lemma successive_full_rows_binary (m : ℕ) (r : Fin (m + 1) → E) (R : Fin (m + 2) → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (hR : ∀ i j, star (R i) * R j = if i = j then 1 else 0)
    (hrsum : (∑ i, r i * star (r i)) = 1)
    (hRsum : (∑ i, R i * star (R i)) = 1) :
    ∃ A B : E, star A * A = 1 ∧ star B * B = 1 ∧ star A * B = 0 ∧
      A * star A + B * star B = 1 ∧ B = R 1 ∧
      ∀ i : Fin m, A * r i.succ = R i.succ.succ := by
  let y : Fin (m + 1) → E := fun i => R (skipSecond m i)
  have hy (i j : Fin (m + 1)) : star (y i) * y j = if i = j then 1 else 0 := by
    simpa only [y, (skipSecond_injective m).eq_iff] using hR (skipSecond m i) (skipSecond m j)
  have hyB (i : Fin (m + 1)) : star (y i) * R 1 = 0 := by
    simpa only [y, skipSecond_ne_one, ite_false] using hR (skipSecond m i) 1
  have hysum : (∑ i, y i * star (y i)) + R 1 * star (R 1) = 1 := by
    rw [← hRsum]
    simp only [y, Fin.sum_univ_succ, skipSecond, Fin.cases_zero, Fin.cases_succ]
    abel
  let A := finiteCuntzTransfer r y 1
  have hAA : star A * A = 1 := by
    simpa only [A, star_one, one_mul, mul_one, hrsum] using finiteCuntzTransfer_star_mul r y hy 1
  have hAst : star A = finiteCuntzTransfer y r 1 := by
    simpa only [A, star_one] using finiteCuntzTransfer_star r y 1
  have hAA' : A * star A = ∑ i, y i * star (y i) := by
    have h := finiteCuntzTransfer_star_mul y r hr 1
    rw [← hAst, star_star] at h
    simpa only [star_one, one_mul, mul_one] using h
  have hAB : star A * R 1 = 0 := by
    rw [hAst]
    simp only [finiteCuntzTransfer, Finset.sum_mul, mul_assoc, hyB, mul_zero,
      Finset.sum_const_zero]
  refine ⟨A, R 1, hAA, ?_, hAB, ?_, rfl, ?_⟩
  · simpa only [ite_true] using hR 1 1
  · rw [hAA']; exact hysum
  · intro i
    simpa only [A, y, skipSecond, Fin.cases_succ, mul_one] using
      finiteCuntzTransfer_mul r y hr 1 i.succ

/-- Every finite initial segment of the actual stabilized canonical row
extends to a binary pair in its same corner. The empty transition sum at
`m=0` is included. -/
lemma exists_canonicalNegative_binary_pair [Nontrivial E] (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (m : ℕ) :
    ∃ A B : E,
      star A * A = canonicalTailProjection s 1 ∧
      star B * B = canonicalTailProjection s 1 ∧ star A * B = 0 ∧
      A * star A + B * star B = canonicalTailProjection s 1 ∧
      B = canonicalNegativeRow s 0 ∧
      ∀ i : Fin m, A * canonicalNegativeRow s i = canonicalNegativeRow s (i + 1) := by
  let q := canonicalTailProjection s 1
  have hq : star q = q := canonicalTailProjection_star s 1
  have hqq : q * q = q := canonicalTailProjection_idempotent s hs 1
  let : NeZero q := ⟨canonicalTailProjection_ne_zero s hs 1⟩
  obtain ⟨r, hrleaf, hr, hrsum⟩ := exists_canonicalNegative_full_row s hs m
  obtain ⟨R, hRleaf, hR, hRsum⟩ := exists_canonicalNegative_full_row s hs (m + 1)
  have hrs (i : Fin (m + 1)) : q * r i = r i ∧ r i * q = r i :=
    ⟨finiteRow_left_support q r hq hqq hr hrsum i, finiteRow_right_support q r hq hqq hr i⟩
  have hRs (i : Fin (m + 2)) : q * R i = R i ∧ R i * q = R i :=
    ⟨finiteRow_left_support q R hq hqq hR hRsum i, finiteRow_right_support q R hq hqq hR i⟩
  let r' : Fin (m + 1) → ProjectionCorner q hq hqq := fun i =>
    projectionCornerElement q hq hqq (r i) (hrs i)
  let R' : Fin (m + 2) → ProjectionCorner q hq hqq := fun i =>
    projectionCornerElement q hq hqq (R i) (hRs i)
  have hr' := projectionCornerElement_gram q hq hqq r hrs hr
  have hR' := projectionCornerElement_gram q hq hqq R hRs hR
  have hrsum' := projectionCornerElement_range_sum q hq hqq r hrs hrsum
  have hRsum' := projectionCornerElement_range_sum q hq hqq R hRs hRsum
  obtain ⟨A, B, hAA, hBB, hAB, hsum, hB, hshift⟩ :=
    successive_full_rows_binary m r' R' hr' hR' hrsum' hRsum'
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg (fun x : ProjectionCorner q hq hqq => (x : E)) hAA
  · exact congrArg (fun x : ProjectionCorner q hq hqq => (x : E)) hBB
  · exact congrArg (fun x : ProjectionCorner q hq hqq => (x : E)) hAB
  · exact congrArg (fun x : ProjectionCorner q hq hqq => (x : E)) hsum
  · have h := congrArg (fun x : ProjectionCorner q hq hqq => (x : E)) hB
    change (B : E) = R 1 at h
    exact h.trans (hRleaf 0)
  · intro i
    have h := congrArg (fun x : ProjectionCorner q hq hqq => (x : E)) (hshift i)
    change (A : E) * r i.succ = R i.succ.succ at h
    rw [hrleaf, hRleaf] at h
    exact h

lemma exists_canonicalNegative_binary_encoding [Nontrivial E] (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (m : ℕ) :
    ∃ A B : E,
      star A * A = canonicalTailProjection s 1 ∧
      star B * B = canonicalTailProjection s 1 ∧ star A * B = 0 ∧
      A * star A + B * star B = canonicalTailProjection s 1 ∧
      ∀ i ≤ m, A ^ i * B = canonicalNegativeRow s i := by
  obtain ⟨A, B, hAA, hBB, hAB, hsum, hB, hstep⟩ :=
    exists_canonicalNegative_binary_pair s hs m
  refine ⟨A, B, hAA, hBB, hAB, hsum, ?_⟩
  intro i
  induction i with
  | zero => intro _; simpa only [pow_zero, one_mul] using hB
  | succ i ih =>
    intro hi
    rw [pow_succ', mul_assoc, ih (by omega)]
    exact hstep ⟨i, by omega⟩

end WeakPureInfiniteness

end

end OAI
