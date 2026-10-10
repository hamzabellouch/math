import OAI.Analysis.Laughlin.FourBody.Square
import OAI.Analysis.Laughlin.ThreeBody.SourceExpansion

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem rowLevel_sum {A : Type*} [AddCommMonoid A] (t : ℕ) (f : ℕ → A) :
    (∑ T : RowLevel t, f T.val.val) =
      (((List.range 16).filter (fun T => t ≤ T)).map f).sum := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun T : Fin 16 => t ≤ T.val))
    (by simp) (fun T : Fin 16 => f T.val),Finset.sum_filter,
    Fin.sum_univ_eq_sum_range (fun n : ℕ => if t ≤ n then f n else 0) 16]
  have hs (n : ℕ) (g : ℕ → A) : (∑ i ∈ Finset.range n, g i) =
      ((List.range n).map g).sum := by
    induction n with
    | zero => simp
    | succ n ih => simp only [Finset.sum_range_succ,List.range_succ,List.map_append,
        List.sum_append,List.map_singleton,List.sum_singleton,ih]
  rw [hs,list_map_ite_sum]

theorem contractionForm_list {I J : Type*} [Fintype I] (Q : ℕ)
    (L : I → Module.End ℂ (Space Q)) (l : List J) (M : J → Matrix I I ℂ) (x : Space Q) :
    contractionForm Q L (l.map M).sum x = (l.map (fun j => contractionForm Q L (M j) x)).sum := by
  induction l with
  | nil => simp [contractionForm]
  | cons j l ih => simp only [List.map_cons,List.sum_cons,contractionForm_add,ih]

theorem matrix_ofReal_list {I J : Type*} (l : List J) (M : J → Matrix I I ℝ) :
    ((l.map M).sum).map Complex.ofReal = (l.map (fun j => (M j).map Complex.ofReal)).sum := by
  induction l with
  | nil => ext i j; simp
  | cons k l ih =>
    simp only [List.map_cons,List.sum_cons]
    have he (A B : Matrix I I ℝ) : (A+B).map Complex.ofReal =
        A.map Complex.ofReal+B.map Complex.ofReal := by ext i j; simp
    rw [he,ih]

theorem physicalThreeBodyMatrix_row_sum (Q : ℕ) (x : Space Q) :
    contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal) x =
      (Certificate.rows.map (fun row => ∑ T : RowLevel row.1,
        contractionForm Q (sourceThreeEnd Q)
          ((threeBodyLevelMatrix Q row.1 T.val.val row.2.1 row.2.2).map Complex.ofReal) x)).sum := by
  simp only [physicalThreeBodyMatrix,matrix_ofReal_list,contractionForm_list]
  congr 1

theorem physicalPairRowMatrix_Fock (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (ht : row.1 ≤ 7) (x : Space Q) :
    contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
      (physicalPairRowMatrix Q row) x =
      ((row.2.1 : ℂ)/10^7)^2 * (occupationNormSq Q (sourcePairEnd Q row.1 x) : ℂ) := by
  let p : Fin (2*Q-2+1) := ⟨row.1,by omega⟩
  have he (i : Fin (2*Q-2+1)) : i.val=row.1 ↔ i=p := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; subst i; rfl
  simp only [contractionForm,physicalPairRowMatrix,he,ite_mul,zero_mul]
  simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,occupationInner_self]
  rfl

theorem source_rows_normal_two_three (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) :
    (Certificate.rows.map (fun row => (occupationNormSq Q (sourceRowSquareVector Q hQ row x) : ℂ))).sum =
      contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
        (physicalTwoBodyMatrix Q) x +
      contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal) x +
      (Certificate.rows.map (fun row => sourceRowFourForm Q hQ row x)).sum := by
  rw [physicalTwoBodyMatrix,contractionForm_list,physicalThreeBodyMatrix_row_sum]
  have hr (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hrow : row ∈ Certificate.rows) :
      (occupationNormSq Q (sourceRowSquareVector Q hQ row x) : ℂ) =
        contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
          (physicalPairRowMatrix Q row) x +
        (∑ T : RowLevel row.1, contractionForm Q (sourceThreeEnd Q)
          ((threeBodyLevelMatrix Q row.1 T.val.val row.2.1 row.2.2).map Complex.ofReal) x) +
        sourceRowFourForm Q hQ row x := by
    have ht := (source_threeBody_rows_support row hrow).1
    rw [sourceRowSquareVector_normal Q hQ row ht,physicalPairRowMatrix_Fock Q hQ row ht]
  rw [List.map_congr_left hr]
  simp only [List.sum_map_add]

end Laughlin.Fock

end OAI
