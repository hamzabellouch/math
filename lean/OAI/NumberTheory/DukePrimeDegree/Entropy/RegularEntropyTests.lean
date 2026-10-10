import OAI.NumberTheory.DukePrimeDegree.Entropy.DiagonalEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! # Finitely many regular weights suffice for coefficient balance

For the prime-degree application the balance argument does not need the
entropy formula at singular weights. One regular weight and one small
perturbation for each coordinate suffice, together with their negatives.
All positive gaps in these explicit weights are at least log 4.
-/

noncomputable section
open scoped BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets

private def rawEntropyTest (d : ℕ) (a : Option (Fin (d+1))) (i : Fin (d+1)) : ℝ :=
  4 * (i.val : ℝ) + if a = some i then 1 else 0

def regularEntropyTest (d : ℕ) (a : Option (Fin (d+1))) (i : Fin (d+1)) : ℝ :=
  rawEntropyTest d a i - (∑ j, rawEntropyTest d a j) / (d+1)

lemma regularEntropyTest_none (d : ℕ) (i : Fin (d+1)) :
    regularEntropyTest d none i = 4 * regularDiagonalWeights d i := by
  simp only [regularEntropyTest, rawEntropyTest, reduceCtorEq, ite_false,
    add_zero, ←Finset.mul_sum, regularDiagonalWeights]
  ring

lemma regularEntropyTest_sum (d : ℕ) (a : Option (Fin (d+1))) :
    ∑ i, regularEntropyTest d a i = 0 := by
  simp only [regularEntropyTest, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (d+1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma regularEntropyTest_gap (d : ℕ) (a : Option (Fin (d+1)))
    {i j : Fin (d+1)} (hij : i < j) :
    Real.log 4 ≤ regularEntropyTest d a j - regularEntropyTest d a i := by
  have hg : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (Nat.succ_le_of_lt hij)
  have hi : (if a = some i then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hj : 0 ≤ (if a = some j then (1:ℝ) else 0) := by split_ifs <;> norm_num
  have hl : Real.log 4 ≤ (3:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num)
    norm_num at h
    exact h
  dsimp only [regularEntropyTest,rawEntropyTest]
  linarith

private lemma rootEntropyForm_skew {d : ℕ} (w : Fin (d+1) → Fin (d+1) → ℝ)
    (t : Fin (d+1) → ℝ) :
    rootEntropyForm w t - rootEntropyForm w (fun i => -t i) =
      ∑ i, ∑ j, w i j * (t i-t j) := by
  unfold rootEntropyForm
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hh : max (t i-t j) 0 - max (-t i - -t j) 0 = t i-t j := by
    by_cases h : t j ≤ t i
    · rw [max_eq_left (by linarith),max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith),max_eq_left (by linarith)]
      ring
  rw [← mul_sub,hh]

private lemma rootEntropyForm_skew_add {d : ℕ} (w : Fin (d+1) → Fin (d+1) → ℝ)
    (t s : Fin (d+1) → ℝ) :
    rootEntropyForm w (fun i => t i+s i) - rootEntropyForm w (fun i => -(t i+s i)) =
      (rootEntropyForm w t - rootEntropyForm w (fun i => -t i)) +
      (rootEntropyForm w s - rootEntropyForm w (fun i => -s i)) := by
  simp only [rootEntropyForm_skew, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma regularEntropyTest_skew {d : ℕ} (w : Fin (d+1) → Fin (d+1) → ℝ)
    (a : Option (Fin (d+1))) :
    rootEntropyForm w (regularEntropyTest d a) -
      rootEntropyForm w (fun i => -regularEntropyTest d a i) =
    rootEntropyForm w (rawEntropyTest d a) -
      rootEntropyForm w (fun i => -rawEntropyTest d a i) := by
  rw [rootEntropyForm_skew,rootEntropyForm_skew]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [regularEntropyTest]
  ring

/-- Balance needs only the explicit finite regular test family and its
negatives, not the formula on arbitrary or singular diagonal weights. -/
theorem balanced_of_regularEntropyTest_symmetry {d : ℕ}
    (w : Fin (d+1) → Fin (d+1) → ℝ)
    (hsym : ∀ a : Option (Fin (d+1)),
      rootEntropyForm w (regularEntropyTest d a) =
        rootEntropyForm w (fun i => -regularEntropyTest d a i)) :
    ∀ i, ∑ j, w i j = ∑ j, w j i := by
  intro a
  have h0 : rootEntropyForm w (rawEntropyTest d none) -
      rootEntropyForm w (fun i => -rawEntropyTest d none i) = 0 := by
    rw [←regularEntropyTest_skew,hsym,sub_self]
  have ha : rootEntropyForm w (rawEntropyTest d (some a)) -
      rootEntropyForm w (fun i => -rawEntropyTest d (some a) i) = 0 := by
    rw [←regularEntropyTest_skew,hsym,sub_self]
  have htest : rawEntropyTest d (some a) =
      fun i => rawEntropyTest d none i + if i=a then 1 else 0 := by
    funext i
    simp only [rawEntropyTest,Option.some.injEq,reduceCtorEq,ite_false,add_zero]
    by_cases hi : i=a
    · subst i
      simp
    · simp [hi,Ne.symm hi]
  rw [htest,rootEntropyForm_skew_add,h0,zero_add,
    rootEntropyForm_indicator,rootEntropyForm_neg_indicator] at ha
  linarith

/-- The finite test formulas are the only entropy identities needed by
coefficient balance, together with invariance of entropy under time reversal. -/
theorem balanced_of_regular_diagonal_entropy_tests
    (d : ℕ) (μ : MeasureTheory.Measure (PrimeDegreePackets.X (d+1)))
    (hA : ∀ u : PrimeDegreePackets.LogCoordinates d,
      μ.map (fun x => PrimeDegreePackets.rightAction x (PrimeDegreePackets.diagonalFlow u))=μ)
    (w : Fin (d+1) → Fin (d+1) → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (htests : ∀ a : Option (Fin (d+1)),
      PrimeDegreePackets.measureEntropy μ (fun x => PrimeDegreePackets.rightAction x
        (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) 1)) =
          ENNReal.ofReal (rootEntropyForm w (regularEntropyTest d a)) ∧
      PrimeDegreePackets.measureEntropy μ (fun x => PrimeDegreePackets.rightAction x
        (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) (-1))) =
          ENNReal.ofReal (rootEntropyForm w (fun i => -regularEntropyTest d a i))) :
    ∀ i, ∑ j, w i j = ∑ j, w j i := by
  apply balanced_of_regularEntropyTest_symmetry w
  intro a
  have he : ENNReal.ofReal (rootEntropyForm w (regularEntropyTest d a)) =
      ENNReal.ofReal (rootEntropyForm w (fun i => -regularEntropyTest d a i)) := by
    rw [←(htests a).1,←(htests a).2]
    exact (diagonal_entropy_neg d (regularEntropyTest d a) (regularEntropyTest_sum d a) μ hA 1).symm
  have H := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (rootEntropyForm_nonneg w hw _)] using H

end DukePrimeDegree

end

end OAI
