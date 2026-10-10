import OAI.Analysis.Laughlin.FourBody.Ungroup

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem sourceRowFourEntry_physical (Q : ℕ) (hQ : 25 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hr : row ∈ Certificate.rows)
    (e f : ℕ × ℕ × ℤ) (he : e ∈ row.2.2) (hf : f ∈ row.2.2) (x : Space Q) :
    sourceRowFourEntry Q row.1 e f x = contractionForm Q (sourceFourFamilyEnd Q)
      ((fourBodyTermMatrix Q row.1 e f).map Complex.ofReal) x := by
  obtain ⟨het,he15,he8⟩ := (source_threeBody_rows_support row hr).2 e he
  obtain ⟨hft,hf15,hf8⟩ := (source_threeBody_rows_support row hr).2 f hf
  rw [fourBodyTermMatrix_Fock Q row.1 e f het hft (by omega),sourceRowFourEntry,
    boundedAnnihilate,dite_eq_left (show f.1+f.2.1-row.1 ≤ Q by omega),
    boundedAnnihilate,dite_eq_left (show e.1+e.2.1-row.1 ≤ Q by omega),
    sourceEntryThree_eq Q e (by omega) (by omega),sourceEntryThree_eq Q f (by omega) (by omega)]
  simp only [sourceFourEnd,Module.End.mul_apply,Complex.ofReal_mul]
  ring

theorem source_rows_four_form (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    (Certificate.rows.map (fun row => sourceRowFourForm Q (by omega) row x)).sum =
      contractionForm Q (sourceFourFamilyEnd Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) x := by
  simp only [physicalFourBodyMatrix,matrix_ofReal_list,contractionForm_list]
  congr 1
  apply List.map_congr_left
  intro row hr
  rw [sourceRowFourForm_entries Q (by omega) row hr]
  congr 1
  apply List.map_congr_left
  intro e he
  congr 1
  apply List.map_congr_left
  intro f hf
  exact sourceRowFourEntry_physical Q hQ row hr e f he hf x

theorem source_seven_squares_normal_form (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    (Certificate.rows.map (fun row => (occupationNormSq Q
      (sourceRowSquareVector Q (by omega) row x) : ℂ))).sum =
      contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
        (physicalTwoBodyMatrix Q) x +
      contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal) x +
      contractionForm Q (sourceFourFamilyEnd Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) x := by
  rw [source_rows_normal_two_three Q (by omega),source_rows_four_form Q hQ]

theorem source_seven_normal_form_nonneg (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    0 ≤ (contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
        (physicalTwoBodyMatrix Q) x +
      contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal) x +
      contractionForm Q (sourceFourFamilyEnd Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) x).re := by
  rw [← source_seven_squares_normal_form Q hQ]
  have hl (l : List (ℕ × ℤ × List (ℕ × ℕ × ℤ))) :
      0 ≤ (l.map (fun row => (occupationNormSq Q (sourceRowSquareVector Q (by omega) row x) : ℂ))).sum.re := by
    induction l with
    | nil => simp
    | cons row l ih =>
      simp only [List.map_cons,List.sum_cons,Complex.add_re,Complex.ofReal_re]
      exact add_nonneg (occupationNormSq_nonneg Q _) ih
  exact hl _

end Laughlin.Fock

end OAI
