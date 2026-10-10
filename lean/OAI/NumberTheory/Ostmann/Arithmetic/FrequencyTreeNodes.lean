import Mathlib.Data.List.GetD
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticFrequencyTree
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticSplitTreeSupport

namespace OAI

/-! # Preorder frequency data and its exact product of split costs -/

namespace Ostmann

open scoped BigOperators Classical

def pairedNodeFrequencies (S : Finset ℤ) (root left right : S × S) :
    NodeFrequencies × NodeFrequencies :=
  (⟨root.1, left.1, right.1⟩, ⟨root.2, left.2, right.2⟩)

theorem pairedNodeFrequencies_bound (S : Finset ℤ) (D : ℝ) (root left right : S × S) :
    pairFrequencySupportBound D (pairedNodeFrequencies S root left right) =
      pairedFrequencyKernel S D root left right := by
  simp only [pairFrequencySupportBound, pairedNodeFrequencies, NodeFrequencies.reducedModulus,
    pairedFrequencyKernel, div_eq_mul_inv]

def frequencySplitList (S : Finset ℤ) : (n : ℕ) →
    FrequencyTree (S × S) n → List (NodeFrequencies × NodeFrequencies)
  | 0, _ => []
  | n + 1, x => pairedNodeFrequencies S x.1 (frequencyRoot n x.2.1) (frequencyRoot n x.2.2) ::
      (frequencySplitList S n x.2.1 ++ frequencySplitList S n x.2.2)

theorem frequencySplitList_length (S : Finset ℤ) (n : ℕ) (x : FrequencyTree (S × S) n) :
    (frequencySplitList S n x).length = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [frequencySplitList, List.length_cons, List.length_append, ih]
    have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega

noncomputable def frequencyLeafWeight {A : Type} (W : A → ℝ) :
    (n : ℕ) → FrequencyTree A n → ℝ
  | 0, x => W x
  | n + 1, x => frequencyLeafWeight W n x.2.1 * frequencyLeafWeight W n x.2.2

theorem frequencyLeafWeight_nonneg {A : Type} (W : A → ℝ) (hW : ∀ a, 0 ≤ W a)
    (n : ℕ) (x : FrequencyTree A n) : 0 ≤ frequencyLeafWeight W n x := by
  induction n with
  | zero => exact hW x
  | succ n ih => exact mul_nonneg (ih _) (ih _)

theorem frequencyTreeWeight_eq_splitList (S : Finset ℤ) (D : ℝ) (W : S × S → ℝ)
    (n : ℕ) (x : FrequencyTree (S × S) n) :
    frequencyTreeWeight (pairedFrequencyKernel S D) W n x =
      ((frequencySplitList S n x).map (pairFrequencySupportBound D)).prod *
        frequencyLeafWeight W n x := by
  induction n with
  | zero => simp [frequencyTreeWeight, frequencySplitList, frequencyLeafWeight]
  | succ n ih =>
    simp only [frequencyTreeWeight, frequencySplitList, frequencyLeafWeight,
      List.map_cons, List.map_append, List.prod_cons, List.prod_append,
      pairedNodeFrequencies_bound, ih]
    ring

theorem prod_range_list_getD {A : Type} (l : List A) (d : A) (f : A → ℝ) :
    (∏ j ∈ Finset.range l.length, f (l.getD j d)) = (l.map f).prod := by
  rw [← Fin.prod_univ_eq_prod_range]
  calc
    _ = ∏ i : Fin l.length, f l[i.val] := by
      apply Finset.prod_congr rfl
      intro i _
      rw [List.getD_eq_getElem l d i.isLt]
    _ = _ := Fin.prod_univ_fun_getElem l f

def emptyNodeFrequencies : NodeFrequencies := ⟨0, 0, 0⟩

def treeNodeFrequencies (S : Finset ℤ) (n : ℕ) (x : FrequencyTree (S × S) n)
    (j : ℕ) : NodeFrequencies × NodeFrequencies :=
  (frequencySplitList S n x).getD j (emptyNodeFrequencies, emptyNodeFrequencies)

theorem pairedNodeFrequencies_moduli_bounds (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) (root left right : S × S) :
    (pairedNodeFrequencies S root left right).1.reducedModulus ∈ Finset.Icc 1 N ∧
      (pairedNodeFrequencies S root left right).2.reducedModulus ∈ Finset.Icc 1 N := by
  constructor
  · apply reducedFrequency_mem
    exact Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr (hS _ root.1.property).1,
      (hS _ root.1.property).2⟩
  · apply reducedFrequency_mem
    exact Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr (hS _ root.2.property).1,
      (hS _ root.2.property).2⟩

theorem frequencySplitList_moduli_bounds (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) (n : ℕ) (x : FrequencyTree (S × S) n)
    (f : NodeFrequencies × NodeFrequencies) (hf : f ∈ frequencySplitList S n x) :
    f.1.reducedModulus ∈ Finset.Icc 1 N ∧ f.2.reducedModulus ∈ Finset.Icc 1 N := by
  induction n with
  | zero => simp [frequencySplitList] at hf
  | succ n ih =>
    simp only [frequencySplitList, List.mem_cons, List.mem_append] at hf
    rcases hf with rfl | hf | hf
    · exact pairedNodeFrequencies_moduli_bounds S N hS _ _ _
    · exact ih _ hf
    · exact ih _ hf

theorem treeNodeFrequencies_divisor_bound (S : Finset ℤ) (N : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (n : ℕ) (x : FrequencyTree (S × S) n) (j : ℕ) :
    (((treeNodeFrequencies S n x j).1.reducedModulus.lcm
      (treeNodeFrequencies S n x j).2.reducedModulus).divisors.card : ℝ) ≤ D := by
  by_cases hj : j < (frequencySplitList S n x).length
  · have hmem : treeNodeFrequencies S n x j ∈ frequencySplitList S n x := by
      rw [treeNodeFrequencies, List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    obtain ⟨ha, hb⟩ := frequencySplitList_moduli_bounds S N hS n x _ hmem
    apply hdiv
    · exact Nat.lcm_ne_zero (Nat.ne_of_gt (Finset.mem_Icc.mp ha).1)
        (Nat.ne_of_gt (Finset.mem_Icc.mp hb).1)
    · exact (Nat.lcm_le_mul (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1).trans (by
        rw [pow_two]
        exact Nat.mul_le_mul (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hb).2)
  · rw [treeNodeFrequencies, List.getD_eq_default _ _ (by omega)]
    simpa [emptyNodeFrequencies, NodeFrequencies.reducedModulus, reducedFrequency] using hD

end Ostmann

end OAI
