import OAI.Analysis.MarkovType.OrderedSequences
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Normed.Group.Basic

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

theorem ofArray_apply_of_ge {m : ℕ} (a : Fin m → ℝ) (j : ℕ) (hj : m ≤ j) :
    ofArray a j = 0 := by
  classical
  simp only [ofArray, place, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hne : i.val ≠ j := Nat.ne_of_lt (lt_of_lt_of_le i.isLt hj)
  simp only [Finsupp.single_apply, ite_eq_right hne]

theorem ofArray_of_vanishes (x : C00) (B : ℕ)
    (hx : ∀ k, B ≤ k → x k = 0) :
    ofArray (fun i : Fin B => x i.val) = x := by
  ext k
  by_cases hk : k < B
  · exact ofArray_apply (fun i : Fin B => x i.val) ⟨k, hk⟩
  · have hBk : B ≤ k := Nat.le_of_not_gt hk
    rw [ofArray_apply_of_ge _ k hBk, hx k hBk]

theorem exists_ofArray (x : C00) :
    ∃ m : ℕ, ∃ a : Fin m → ℝ, ofArray a = x := by
  classical
  let m := (x.support.sup id).succ
  refine ⟨m, (fun i => x i.val), ?_⟩
  ext j
  by_cases hj : j < m
  · exact ofArray_apply (fun i : Fin m => x i.val) ⟨j, hj⟩
  · have hmj : m ≤ j := Nat.le_of_not_gt hj
    rw [ofArray_apply_of_ge _ j hmj]
    symm
    apply Finsupp.notMem_support_iff.mp
    intro hs
    have hlt : j < m :=
      Finset.mem_range.mp (Finset.subset_range_sup_succ x.support hs)
    exact hj hlt

theorem smul_basis (r : ℝ) (i : ℕ) : r • basis i = Finsupp.single i r := by
  simp [basis]

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem linearMap_ofArray (L : C00 →ₗ[ℝ] Y) {m : ℕ} (a : Fin m → ℝ) :
    L (ofArray a) = ∑ i, a i • L (basis i.val) := by
  simp only [ofArray, place, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_basis, map_smul]

theorem norm_linearMap_ofArray_le (L : C00 →ₗ[ℝ] Y)
    (hunit : ∀ i, ‖L (basis i)‖ ≤ 1) {m : ℕ} (a : Fin m → ℝ) :
    ‖L (ofArray a)‖ ≤ ∑ i, |a i| := by
  rw [linearMap_ofArray]
  calc
    ‖∑ i, a i • L (basis i.val)‖ ≤ ∑ i, ‖a i • L (basis i.val)‖ :=
      norm_sum_le _ _
    _ = ∑ i, |a i| * ‖L (basis i.val)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |a i| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hunit i.val) (abs_nonneg (a i))

theorem abs_norm_linearMap_ofArray_sub_le (L : C00 →ₗ[ℝ] Y)
    (hunit : ∀ i, ‖L (basis i)‖ ≤ 1) {m : ℕ} (a b : Fin m → ℝ) :
    |‖L (ofArray a)‖ - ‖L (ofArray b)‖| ≤ ∑ i, |a i - b i| := by
  calc
    |‖L (ofArray a)‖ - ‖L (ofArray b)‖| ≤ ‖L (ofArray a) - L (ofArray b)‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖L (ofArray (a - b))‖ := by
      rw [← map_sub]
      congr 2
      exact (map_sub (arrayLinear m) a b).symm
    _ ≤ ∑ i, |a i - b i| := norm_linearMap_ofArray_le L hunit (a - b)

end C00

end MarkovSuperreflexivity

end

end OAI
