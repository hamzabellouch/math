import OAI.Analysis.MutuallyUnbiased.MixedSemantics.GroupedColumns

namespace OAI

/-! Explicit four-column grouping formulas for the fifteen equality patterns
used by the exact pair certificate. -/

open scoped BigOperators
namespace MUB6

theorem groupedColumns_family4_0 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 0) =
      (fun i => ![A i 0 + A i 1 + A i 2 + A i 3]) := by
  change groupedColumns A (![0, 0, 0, 0] : Fin 4 → Fin 1) = _
  ext i b
  fin_cases b
  simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ, add_assoc]

theorem groupedColumns_family4_1 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 1) =
      (fun i => ![A i 0 + A i 1 + A i 2, A i 3]) := by
  change groupedColumns A (![0, 0, 0, 1] : Fin 4 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ, add_assoc]

theorem groupedColumns_family4_2 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 2) =
      (fun i => ![A i 0 + A i 1 + A i 3, A i 2]) := by
  change groupedColumns A (![0, 0, 1, 0] : Fin 4 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ, add_assoc]

theorem groupedColumns_family4_3 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 3) =
      (fun i => ![A i 0 + A i 1, A i 2 + A i 3]) := by
  change groupedColumns A (![0, 0, 1, 1] : Fin 4 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family4_4 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 4) =
      (fun i => ![A i 0 + A i 1, A i 2, A i 3]) := by
  change groupedColumns A (![0, 0, 1, 2] : Fin 4 → Fin 3) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family4_5 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 5) =
      (fun i => ![A i 0 + A i 2 + A i 3, A i 1]) := by
  change groupedColumns A (![0, 1, 0, 0] : Fin 4 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ, add_assoc]

theorem groupedColumns_family4_6 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 6) =
      (fun i => ![A i 0 + A i 2, A i 1 + A i 3]) := by
  change groupedColumns A (![0, 1, 0, 1] : Fin 4 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family4_7 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 7) =
      (fun i => ![A i 0 + A i 2, A i 1, A i 3]) := by
  change groupedColumns A (![0, 1, 0, 2] : Fin 4 → Fin 3) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family4_8 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 8) =
      (fun i => ![A i 0 + A i 3, A i 1 + A i 2]) := by
  change groupedColumns A (![0, 1, 1, 0] : Fin 4 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family4_9 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 9) =
      (fun i => ![A i 0, A i 1 + A i 2 + A i 3]) := by
  change groupedColumns A (![0, 1, 1, 1] : Fin 4 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ, add_assoc]

theorem groupedColumns_family4_10 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 10) =
      (fun i => ![A i 0, A i 1 + A i 2, A i 3]) := by
  change groupedColumns A (![0, 1, 1, 2] : Fin 4 → Fin 3) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family4_11 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 11) =
      (fun i => ![A i 0 + A i 3, A i 1, A i 2]) := by
  change groupedColumns A (![0, 1, 2, 0] : Fin 4 → Fin 3) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family4_12 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 12) =
      (fun i => ![A i 0, A i 1 + A i 3, A i 2]) := by
  change groupedColumns A (![0, 1, 2, 1] : Fin 4 → Fin 3) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family4_13 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 13) =
      (fun i => ![A i 0, A i 1, A i 2 + A i 3]) := by
  change groupedColumns A (![0, 1, 2, 2] : Fin 4 → Fin 3) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family4_14 {p : ℕ} (A : Matrix (Fin p) (Fin 4) ℤ) :
    groupedColumns A (EqualityPatterns.family4.label 14) =
      (fun i => ![A i 0, A i 1, A i 2, A i 3]) := by
  change groupedColumns A (![0, 1, 2, 3] : Fin 4 → Fin 4) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

end MUB6

end OAI
