import OAI.Analysis.MarkovType.TriangularArrays
import OAI.Analysis.MarkovType.OrderedSequences
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

universe u

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def coefficientL1 {m : ℕ} (a : Fin m → ℝ) : ℝ := ∑ i, |a i|

theorem coefficientL1_nonneg {m : ℕ} (a : Fin m → ℝ) : 0 ≤ coefficientL1 a :=
  Finset.sum_nonneg fun i _ => abs_nonneg (a i)

def arrayPrefix {m : ℕ} (a : Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ i, if i.val < k then a i else 0

theorem prefixCut_ofArray {m : ℕ} (a : Fin m → ℝ) (k : ℕ) :
    prefixCut (C00.ofArray a) k = arrayPrefix a k := by
  classical
  simp only [prefixCut, C00.ofArray, C00.place, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq, Finset.mem_range, arrayPrefix]

theorem triangular_combination_upper {M m : ℕ} {d ε : ℝ}
    (A : TriangularArray Y d ε M) (idx : Fin m → Fin M) (a : Fin m → ℝ) :
    ‖∑ i, a i • A.y (idx i)‖ ≤ coefficientL1 a := by
  calc
    ‖∑ i, a i • A.y (idx i)‖ ≤ ∑ i, ‖a i • A.y (idx i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, |a i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (A.y_norm_le (idx i)) (abs_nonneg (a i))).trans_eq
        (mul_one _)
    _ = coefficientL1 a := rfl

theorem triangular_prefix_lower {M m : ℕ} {d ε : ℝ}
    (A : TriangularArray Y d ε M) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (idx : Fin m → Fin M) (hidx : StrictAnti idx) (a : Fin m → ℝ) (k : ℕ) :
    d * |arrayPrefix a k| - ε * coefficientL1 a ≤
      ‖∑ i, a i • A.y (idx i)‖ := by
  classical
  by_cases hm : m = 0
  · subst m
    simp [arrayPrefix, coefficientL1]
  by_cases hk : k = 0
  · have hnonneg := mul_nonneg hε (coefficientL1_nonneg a)
    have hnorm := norm_nonneg (∑ i, a i • A.y (idx i))
    simp only [hk, arrayPrefix, Nat.not_lt_zero, ite_false, Finset.sum_const_zero,
      abs_zero, mul_zero]
    linarith
  have hmin_pos : 0 < min k m := by omega
  let j : Fin m := ⟨min k m - 1, by have := min_le_right k m; omega⟩
  let F : Y →L[ℝ] ℝ := A.f (idx j)
  let S : Y := ∑ i, a i • A.y (idx i)
  have herr (i : Fin m) :
      |F (A.y (idx i)) - (if i.val < k then d else 0)| ≤ ε := by
    by_cases hi : i.val < k
    · rw [ite_eq_left hi]
      have hij : i ≤ j := by
        change i.val ≤ min k m - 1
        have := i.isLt
        omega
      exact A.upper_close (idx j) (idx i) (hidx.antitone hij)
    · rw [ite_eq_right hi]
      have hji : j < i := by
        change min k m - 1 < i.val
        have := min_le_left k m
        omega
      have hzero : F (A.y (idx i)) = 0 := A.lower_zero (idx j) (idx i) (hidx hji)
      rw [hzero, sub_zero, abs_zero]
      exact hε
  have hidentity :
      F S - d * arrayPrefix a k =
        ∑ i, a i * (F (A.y (idx i)) - (if i.val < k then d else 0)) := by
    calc
      F S - d * arrayPrefix a k =
          (∑ i, a i * F (A.y (idx i))) -
            ∑ i, d * (if i.val < k then a i else 0) := by
        simp only [S, map_sum, map_smul, smul_eq_mul, arrayPrefix, Finset.mul_sum]
      _ = ∑ i, (a i * F (A.y (idx i)) - d * (if i.val < k then a i else 0)) := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
  have herror : |F S - d * arrayPrefix a k| ≤ ε * coefficientL1 a := by
    rw [hidentity]
    calc
      |∑ i, a i * (F (A.y (idx i)) - (if i.val < k then d else 0))|
          ≤ ∑ i, |a i * (F (A.y (idx i)) - (if i.val < k then d else 0))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |a i| * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (herr i) (abs_nonneg (a i))
      _ = ε * coefficientL1 a := by
        rw [← Finset.sum_mul]
        exact mul_comm _ _
  have hF : |F S| ≤ ‖S‖ := by
    simpa only [Real.norm_eq_abs, one_mul] using
      F.le_of_opNorm_le (A.f_norm_le (idx j)) S
  have htriangle : |d * arrayPrefix a k| ≤ |F S| + |F S - d * arrayPrefix a k| := by
    calc
      |d * arrayPrefix a k| = |F S - (F S - d * arrayPrefix a k)| := by congr 1; ring
      _ ≤ |F S| + |F S - d * arrayPrefix a k| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (F S) (-(F S - d * arrayPrefix a k))
  rw [abs_mul, abs_of_nonneg hd] at htriangle
  change d * |arrayPrefix a k| - ε * coefficientL1 a ≤ ‖S‖
  linarith

theorem triangular_prefixCut_lower {M m : ℕ} {d ε : ℝ}
    (A : TriangularArray Y d ε M) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (idx : Fin m → Fin M) (hidx : StrictAnti idx) (a : Fin m → ℝ) (k : ℕ) :
    d * |prefixCut (C00.ofArray a) k| - ε * coefficientL1 a ≤
      ‖∑ i, a i • A.y (idx i)‖ := by
  rw [prefixCut_ofArray]
  exact triangular_prefix_lower A hd hε idx hidx a k

theorem reversed_triangular_prefixCut_lower {M m : ℕ} {d ε : ℝ}
    (A : TriangularArray Y d ε M) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (idx : Fin m → Fin M) (hidx : StrictMono idx) (a : Fin m → ℝ) (k : ℕ) :
    d * |prefixCut (C00.ofArray a) k| - ε * coefficientL1 a ≤
      ‖∑ i, a i • A.y (Fin.rev (idx i))‖ := by
  apply triangular_prefixCut_lower A hd hε (fun i => Fin.rev (idx i)) _ a k
  intro i j hij
  exact Fin.rev_lt_rev.mpr (hidx hij)

end MarkovSuperreflexivity

end

end OAI
