import Mathlib.Tactic.FinCases
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRowsAll

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedCanonicalPCoeff (r : Fin 49) (i : ℕ) : ℤ :=
  match r.val with
  | 0 => fixedRowPCoeff_0 i
  | 1 => fixedRowPCoeff_1 i
  | 2 => fixedRowPCoeff_2 i
  | 3 => fixedRowPCoeff_3 i
  | 4 => fixedRowPCoeff_4 i
  | 5 => fixedRowPCoeff_5 i
  | 6 => fixedRowPCoeff_6 i
  | 7 => fixedRowPCoeff_7 i
  | 8 => fixedRowPCoeff_8 i
  | 9 => fixedRowPCoeff_9 i
  | 10 => fixedRowPCoeff_10 i
  | 11 => fixedRowPCoeff_11 i
  | 12 => fixedRowPCoeff_12 i
  | 13 => fixedRowPCoeff_13 i
  | 14 => fixedRowPCoeff_14 i
  | 15 => fixedRowPCoeff_15 i
  | 16 => fixedRowPCoeff_16 i
  | 17 => fixedRowPCoeff_17 i
  | 18 => fixedRowPCoeff_18 i
  | 19 => fixedRowPCoeff_19 i
  | 20 => fixedRowPCoeff_20 i
  | 21 => fixedRowPCoeff_21 i
  | 22 => fixedRowPCoeff_22 i
  | 23 => fixedRowPCoeff_23 i
  | 24 => fixedRowPCoeff_24 i
  | 25 => fixedRowPCoeff_25 i
  | 26 => fixedRowPCoeff_26 i
  | 27 => fixedRowPCoeff_27 i
  | 28 => fixedRowPCoeff_28 i
  | 29 => fixedRowPCoeff_29 i
  | 30 => fixedRowPCoeff_30 i
  | 31 => fixedRowPCoeff_31 i
  | 32 => fixedRowPCoeff_32 i
  | 33 => fixedRowPCoeff_33 i
  | 34 => fixedRowPCoeff_34 i
  | 35 => fixedRowPCoeff_35 i
  | 36 => fixedRowPCoeff_36 i
  | 37 => fixedRowPCoeff_37 i
  | 38 => fixedRowPCoeff_38 i
  | 39 => fixedRowPCoeff_39 i
  | 40 => fixedRowPCoeff_40 i
  | 41 => fixedRowPCoeff_41 i
  | 42 => fixedRowPCoeff_42 i
  | 43 => fixedRowPCoeff_43 i
  | 44 => fixedRowPCoeff_44 i
  | 45 => fixedRowPCoeff_45 i
  | 46 => fixedRowPCoeff_46 i
  | 47 => fixedRowPCoeff_47 i
  | 48 => fixedRowPCoeff_48 i
  | _ => 0

theorem fixedCanonicalPCoeff_eq (r : Fin 49) (i : ℕ) :
    (rowP 1 r.val).coeff i = fixedCanonicalPCoeff r i := by
  fin_cases r
  · change (rowP 1 0).coeff i = fixedRowPCoeff_0 i
    rw [fixed_rowP_typed_0]
    exact fixed_rowP_typed_coeff_0 i
  · change (rowP 1 1).coeff i = fixedRowPCoeff_1 i
    rw [fixed_rowP_typed_1]
    exact fixed_rowP_typed_coeff_1 i
  · change (rowP 1 2).coeff i = fixedRowPCoeff_2 i
    rw [fixed_rowP_typed_2]
    exact fixed_rowP_typed_coeff_2 i
  · change (rowP 1 3).coeff i = fixedRowPCoeff_3 i
    rw [fixed_rowP_typed_3]
    exact fixed_rowP_typed_coeff_3 i
  · change (rowP 1 4).coeff i = fixedRowPCoeff_4 i
    rw [fixed_rowP_typed_4]
    exact fixed_rowP_typed_coeff_4 i
  · change (rowP 1 5).coeff i = fixedRowPCoeff_5 i
    rw [fixed_rowP_typed_5]
    exact fixed_rowP_typed_coeff_5 i
  · change (rowP 1 6).coeff i = fixedRowPCoeff_6 i
    rw [fixed_rowP_typed_6]
    exact fixed_rowP_typed_coeff_6 i
  · change (rowP 1 7).coeff i = fixedRowPCoeff_7 i
    rw [fixed_rowP_typed_7]
    exact fixed_rowP_typed_coeff_7 i
  · change (rowP 1 8).coeff i = fixedRowPCoeff_8 i
    rw [fixed_rowP_typed_8]
    exact fixed_rowP_typed_coeff_8 i
  · change (rowP 1 9).coeff i = fixedRowPCoeff_9 i
    rw [fixed_rowP_typed_9]
    exact fixed_rowP_typed_coeff_9 i
  · change (rowP 1 10).coeff i = fixedRowPCoeff_10 i
    rw [fixed_rowP_typed_10]
    exact fixed_rowP_typed_coeff_10 i
  · change (rowP 1 11).coeff i = fixedRowPCoeff_11 i
    rw [fixed_rowP_typed_11]
    exact fixed_rowP_typed_coeff_11 i
  · change (rowP 1 12).coeff i = fixedRowPCoeff_12 i
    rw [fixed_rowP_typed_12]
    exact fixed_rowP_typed_coeff_12 i
  · change (rowP 1 13).coeff i = fixedRowPCoeff_13 i
    rw [fixed_rowP_typed_13]
    exact fixed_rowP_typed_coeff_13 i
  · change (rowP 1 14).coeff i = fixedRowPCoeff_14 i
    rw [fixed_rowP_typed_14]
    exact fixed_rowP_typed_coeff_14 i
  · change (rowP 1 15).coeff i = fixedRowPCoeff_15 i
    rw [fixed_rowP_typed_15]
    exact fixed_rowP_typed_coeff_15 i
  · change (rowP 1 16).coeff i = fixedRowPCoeff_16 i
    rw [fixed_rowP_typed_16]
    exact fixed_rowP_typed_coeff_16 i
  · change (rowP 1 17).coeff i = fixedRowPCoeff_17 i
    rw [fixed_rowP_typed_17]
    exact fixed_rowP_typed_coeff_17 i
  · change (rowP 1 18).coeff i = fixedRowPCoeff_18 i
    rw [fixed_rowP_typed_18]
    exact fixed_rowP_typed_coeff_18 i
  · change (rowP 1 19).coeff i = fixedRowPCoeff_19 i
    rw [fixed_rowP_typed_19]
    exact fixed_rowP_typed_coeff_19 i
  · change (rowP 1 20).coeff i = fixedRowPCoeff_20 i
    rw [fixed_rowP_typed_20]
    exact fixed_rowP_typed_coeff_20 i
  · change (rowP 1 21).coeff i = fixedRowPCoeff_21 i
    rw [fixed_rowP_typed_21]
    exact fixed_rowP_typed_coeff_21 i
  · change (rowP 1 22).coeff i = fixedRowPCoeff_22 i
    rw [fixed_rowP_typed_22]
    exact fixed_rowP_typed_coeff_22 i
  · change (rowP 1 23).coeff i = fixedRowPCoeff_23 i
    rw [fixed_rowP_typed_23]
    exact fixed_rowP_typed_coeff_23 i
  · change (rowP 1 24).coeff i = fixedRowPCoeff_24 i
    rw [fixed_rowP_typed_24]
    exact fixed_rowP_typed_coeff_24 i
  · change (rowP 1 25).coeff i = fixedRowPCoeff_25 i
    rw [fixed_rowP_typed_25]
    exact fixed_rowP_typed_coeff_25 i
  · change (rowP 1 26).coeff i = fixedRowPCoeff_26 i
    rw [fixed_rowP_typed_26]
    exact fixed_rowP_typed_coeff_26 i
  · change (rowP 1 27).coeff i = fixedRowPCoeff_27 i
    rw [fixed_rowP_typed_27]
    exact fixed_rowP_typed_coeff_27 i
  · change (rowP 1 28).coeff i = fixedRowPCoeff_28 i
    rw [fixed_rowP_typed_28]
    exact fixed_rowP_typed_coeff_28 i
  · change (rowP 1 29).coeff i = fixedRowPCoeff_29 i
    rw [fixed_rowP_typed_29]
    exact fixed_rowP_typed_coeff_29 i
  · change (rowP 1 30).coeff i = fixedRowPCoeff_30 i
    rw [fixed_rowP_typed_30]
    exact fixed_rowP_typed_coeff_30 i
  · change (rowP 1 31).coeff i = fixedRowPCoeff_31 i
    rw [fixed_rowP_typed_31]
    exact fixed_rowP_typed_coeff_31 i
  · change (rowP 1 32).coeff i = fixedRowPCoeff_32 i
    rw [fixed_rowP_typed_32]
    exact fixed_rowP_typed_coeff_32 i
  · change (rowP 1 33).coeff i = fixedRowPCoeff_33 i
    rw [fixed_rowP_typed_33]
    exact fixed_rowP_typed_coeff_33 i
  · change (rowP 1 34).coeff i = fixedRowPCoeff_34 i
    rw [fixed_rowP_typed_34]
    exact fixed_rowP_typed_coeff_34 i
  · change (rowP 1 35).coeff i = fixedRowPCoeff_35 i
    rw [fixed_rowP_typed_35]
    exact fixed_rowP_typed_coeff_35 i
  · change (rowP 1 36).coeff i = fixedRowPCoeff_36 i
    rw [fixed_rowP_typed_36]
    exact fixed_rowP_typed_coeff_36 i
  · change (rowP 1 37).coeff i = fixedRowPCoeff_37 i
    rw [fixed_rowP_typed_37]
    exact fixed_rowP_typed_coeff_37 i
  · change (rowP 1 38).coeff i = fixedRowPCoeff_38 i
    rw [fixed_rowP_typed_38]
    exact fixed_rowP_typed_coeff_38 i
  · change (rowP 1 39).coeff i = fixedRowPCoeff_39 i
    rw [fixed_rowP_typed_39]
    exact fixed_rowP_typed_coeff_39 i
  · change (rowP 1 40).coeff i = fixedRowPCoeff_40 i
    rw [fixed_rowP_typed_40]
    exact fixed_rowP_typed_coeff_40 i
  · change (rowP 1 41).coeff i = fixedRowPCoeff_41 i
    rw [fixed_rowP_typed_41]
    exact fixed_rowP_typed_coeff_41 i
  · change (rowP 1 42).coeff i = fixedRowPCoeff_42 i
    rw [fixed_rowP_typed_42]
    exact fixed_rowP_typed_coeff_42 i
  · change (rowP 1 43).coeff i = fixedRowPCoeff_43 i
    rw [fixed_rowP_typed_43]
    exact fixed_rowP_typed_coeff_43 i
  · change (rowP 1 44).coeff i = fixedRowPCoeff_44 i
    rw [fixed_rowP_typed_44]
    exact fixed_rowP_typed_coeff_44 i
  · change (rowP 1 45).coeff i = fixedRowPCoeff_45 i
    rw [fixed_rowP_typed_45]
    exact fixed_rowP_typed_coeff_45 i
  · change (rowP 1 46).coeff i = fixedRowPCoeff_46 i
    rw [fixed_rowP_typed_46]
    exact fixed_rowP_typed_coeff_46 i
  · change (rowP 1 47).coeff i = fixedRowPCoeff_47 i
    rw [fixed_rowP_typed_47]
    exact fixed_rowP_typed_coeff_47 i
  · change (rowP 1 48).coeff i = fixedRowPCoeff_48 i
    rw [fixed_rowP_typed_48]
    exact fixed_rowP_typed_coeff_48 i

def fixedCanonicalDCoeff (r : Fin 49) (i : ℕ) : ℤ :=
  match r.val with
  | 0 => fixedRowDCoeff_0 i
  | 1 => fixedRowDCoeff_1 i
  | 2 => fixedRowDCoeff_2 i
  | 3 => fixedRowDCoeff_3 i
  | 4 => fixedRowDCoeff_4 i
  | 5 => fixedRowDCoeff_5 i
  | 6 => fixedRowDCoeff_6 i
  | 7 => fixedRowDCoeff_7 i
  | 8 => fixedRowDCoeff_8 i
  | 9 => fixedRowDCoeff_9 i
  | 10 => fixedRowDCoeff_10 i
  | 11 => fixedRowDCoeff_11 i
  | 12 => fixedRowDCoeff_12 i
  | 13 => fixedRowDCoeff_13 i
  | 14 => fixedRowDCoeff_14 i
  | 15 => fixedRowDCoeff_15 i
  | 16 => fixedRowDCoeff_16 i
  | 17 => fixedRowDCoeff_17 i
  | 18 => fixedRowDCoeff_18 i
  | 19 => fixedRowDCoeff_19 i
  | 20 => fixedRowDCoeff_20 i
  | 21 => fixedRowDCoeff_21 i
  | 22 => fixedRowDCoeff_22 i
  | 23 => fixedRowDCoeff_23 i
  | 24 => fixedRowDCoeff_24 i
  | 25 => fixedRowDCoeff_25 i
  | 26 => fixedRowDCoeff_26 i
  | 27 => fixedRowDCoeff_27 i
  | 28 => fixedRowDCoeff_28 i
  | 29 => fixedRowDCoeff_29 i
  | 30 => fixedRowDCoeff_30 i
  | 31 => fixedRowDCoeff_31 i
  | 32 => fixedRowDCoeff_32 i
  | 33 => fixedRowDCoeff_33 i
  | 34 => fixedRowDCoeff_34 i
  | 35 => fixedRowDCoeff_35 i
  | 36 => fixedRowDCoeff_36 i
  | 37 => fixedRowDCoeff_37 i
  | 38 => fixedRowDCoeff_38 i
  | 39 => fixedRowDCoeff_39 i
  | 40 => fixedRowDCoeff_40 i
  | 41 => fixedRowDCoeff_41 i
  | 42 => fixedRowDCoeff_42 i
  | 43 => fixedRowDCoeff_43 i
  | 44 => fixedRowDCoeff_44 i
  | 45 => fixedRowDCoeff_45 i
  | 46 => fixedRowDCoeff_46 i
  | 47 => fixedRowDCoeff_47 i
  | 48 => fixedRowDCoeff_48 i
  | _ => 0

theorem fixedCanonicalDCoeff_eq (r : Fin 49) (i : ℕ) :
    (rowD 1 r.val).coeff i = fixedCanonicalDCoeff r i := by
  fin_cases r
  · change (rowD 1 0).coeff i = fixedRowDCoeff_0 i
    rw [fixed_rowD_typed_0]
    exact fixed_rowD_typed_coeff_0 i
  · change (rowD 1 1).coeff i = fixedRowDCoeff_1 i
    rw [fixed_rowD_typed_1]
    exact fixed_rowD_typed_coeff_1 i
  · change (rowD 1 2).coeff i = fixedRowDCoeff_2 i
    rw [fixed_rowD_typed_2]
    exact fixed_rowD_typed_coeff_2 i
  · change (rowD 1 3).coeff i = fixedRowDCoeff_3 i
    rw [fixed_rowD_typed_3]
    exact fixed_rowD_typed_coeff_3 i
  · change (rowD 1 4).coeff i = fixedRowDCoeff_4 i
    rw [fixed_rowD_typed_4]
    exact fixed_rowD_typed_coeff_4 i
  · change (rowD 1 5).coeff i = fixedRowDCoeff_5 i
    rw [fixed_rowD_typed_5]
    exact fixed_rowD_typed_coeff_5 i
  · change (rowD 1 6).coeff i = fixedRowDCoeff_6 i
    rw [fixed_rowD_typed_6]
    exact fixed_rowD_typed_coeff_6 i
  · change (rowD 1 7).coeff i = fixedRowDCoeff_7 i
    rw [fixed_rowD_typed_7]
    exact fixed_rowD_typed_coeff_7 i
  · change (rowD 1 8).coeff i = fixedRowDCoeff_8 i
    rw [fixed_rowD_typed_8]
    exact fixed_rowD_typed_coeff_8 i
  · change (rowD 1 9).coeff i = fixedRowDCoeff_9 i
    rw [fixed_rowD_typed_9]
    exact fixed_rowD_typed_coeff_9 i
  · change (rowD 1 10).coeff i = fixedRowDCoeff_10 i
    rw [fixed_rowD_typed_10]
    exact fixed_rowD_typed_coeff_10 i
  · change (rowD 1 11).coeff i = fixedRowDCoeff_11 i
    rw [fixed_rowD_typed_11]
    exact fixed_rowD_typed_coeff_11 i
  · change (rowD 1 12).coeff i = fixedRowDCoeff_12 i
    rw [fixed_rowD_typed_12]
    exact fixed_rowD_typed_coeff_12 i
  · change (rowD 1 13).coeff i = fixedRowDCoeff_13 i
    rw [fixed_rowD_typed_13]
    exact fixed_rowD_typed_coeff_13 i
  · change (rowD 1 14).coeff i = fixedRowDCoeff_14 i
    rw [fixed_rowD_typed_14]
    exact fixed_rowD_typed_coeff_14 i
  · change (rowD 1 15).coeff i = fixedRowDCoeff_15 i
    rw [fixed_rowD_typed_15]
    exact fixed_rowD_typed_coeff_15 i
  · change (rowD 1 16).coeff i = fixedRowDCoeff_16 i
    rw [fixed_rowD_typed_16]
    exact fixed_rowD_typed_coeff_16 i
  · change (rowD 1 17).coeff i = fixedRowDCoeff_17 i
    rw [fixed_rowD_typed_17]
    exact fixed_rowD_typed_coeff_17 i
  · change (rowD 1 18).coeff i = fixedRowDCoeff_18 i
    rw [fixed_rowD_typed_18]
    exact fixed_rowD_typed_coeff_18 i
  · change (rowD 1 19).coeff i = fixedRowDCoeff_19 i
    rw [fixed_rowD_typed_19]
    exact fixed_rowD_typed_coeff_19 i
  · change (rowD 1 20).coeff i = fixedRowDCoeff_20 i
    rw [fixed_rowD_typed_20]
    exact fixed_rowD_typed_coeff_20 i
  · change (rowD 1 21).coeff i = fixedRowDCoeff_21 i
    rw [fixed_rowD_typed_21]
    exact fixed_rowD_typed_coeff_21 i
  · change (rowD 1 22).coeff i = fixedRowDCoeff_22 i
    rw [fixed_rowD_typed_22]
    exact fixed_rowD_typed_coeff_22 i
  · change (rowD 1 23).coeff i = fixedRowDCoeff_23 i
    rw [fixed_rowD_typed_23]
    exact fixed_rowD_typed_coeff_23 i
  · change (rowD 1 24).coeff i = fixedRowDCoeff_24 i
    rw [fixed_rowD_typed_24]
    exact fixed_rowD_typed_coeff_24 i
  · change (rowD 1 25).coeff i = fixedRowDCoeff_25 i
    rw [fixed_rowD_typed_25]
    exact fixed_rowD_typed_coeff_25 i
  · change (rowD 1 26).coeff i = fixedRowDCoeff_26 i
    rw [fixed_rowD_typed_26]
    exact fixed_rowD_typed_coeff_26 i
  · change (rowD 1 27).coeff i = fixedRowDCoeff_27 i
    rw [fixed_rowD_typed_27]
    exact fixed_rowD_typed_coeff_27 i
  · change (rowD 1 28).coeff i = fixedRowDCoeff_28 i
    rw [fixed_rowD_typed_28]
    exact fixed_rowD_typed_coeff_28 i
  · change (rowD 1 29).coeff i = fixedRowDCoeff_29 i
    rw [fixed_rowD_typed_29]
    exact fixed_rowD_typed_coeff_29 i
  · change (rowD 1 30).coeff i = fixedRowDCoeff_30 i
    rw [fixed_rowD_typed_30]
    exact fixed_rowD_typed_coeff_30 i
  · change (rowD 1 31).coeff i = fixedRowDCoeff_31 i
    rw [fixed_rowD_typed_31]
    exact fixed_rowD_typed_coeff_31 i
  · change (rowD 1 32).coeff i = fixedRowDCoeff_32 i
    rw [fixed_rowD_typed_32]
    exact fixed_rowD_typed_coeff_32 i
  · change (rowD 1 33).coeff i = fixedRowDCoeff_33 i
    rw [fixed_rowD_typed_33]
    exact fixed_rowD_typed_coeff_33 i
  · change (rowD 1 34).coeff i = fixedRowDCoeff_34 i
    rw [fixed_rowD_typed_34]
    exact fixed_rowD_typed_coeff_34 i
  · change (rowD 1 35).coeff i = fixedRowDCoeff_35 i
    rw [fixed_rowD_typed_35]
    exact fixed_rowD_typed_coeff_35 i
  · change (rowD 1 36).coeff i = fixedRowDCoeff_36 i
    rw [fixed_rowD_typed_36]
    exact fixed_rowD_typed_coeff_36 i
  · change (rowD 1 37).coeff i = fixedRowDCoeff_37 i
    rw [fixed_rowD_typed_37]
    exact fixed_rowD_typed_coeff_37 i
  · change (rowD 1 38).coeff i = fixedRowDCoeff_38 i
    rw [fixed_rowD_typed_38]
    exact fixed_rowD_typed_coeff_38 i
  · change (rowD 1 39).coeff i = fixedRowDCoeff_39 i
    rw [fixed_rowD_typed_39]
    exact fixed_rowD_typed_coeff_39 i
  · change (rowD 1 40).coeff i = fixedRowDCoeff_40 i
    rw [fixed_rowD_typed_40]
    exact fixed_rowD_typed_coeff_40 i
  · change (rowD 1 41).coeff i = fixedRowDCoeff_41 i
    rw [fixed_rowD_typed_41]
    exact fixed_rowD_typed_coeff_41 i
  · change (rowD 1 42).coeff i = fixedRowDCoeff_42 i
    rw [fixed_rowD_typed_42]
    exact fixed_rowD_typed_coeff_42 i
  · change (rowD 1 43).coeff i = fixedRowDCoeff_43 i
    rw [fixed_rowD_typed_43]
    exact fixed_rowD_typed_coeff_43 i
  · change (rowD 1 44).coeff i = fixedRowDCoeff_44 i
    rw [fixed_rowD_typed_44]
    exact fixed_rowD_typed_coeff_44 i
  · change (rowD 1 45).coeff i = fixedRowDCoeff_45 i
    rw [fixed_rowD_typed_45]
    exact fixed_rowD_typed_coeff_45 i
  · change (rowD 1 46).coeff i = fixedRowDCoeff_46 i
    rw [fixed_rowD_typed_46]
    exact fixed_rowD_typed_coeff_46 i
  · change (rowD 1 47).coeff i = fixedRowDCoeff_47 i
    rw [fixed_rowD_typed_47]
    exact fixed_rowD_typed_coeff_47 i
  · change (rowD 1 48).coeff i = fixedRowDCoeff_48 i
    rw [fixed_rowD_typed_48]
    exact fixed_rowD_typed_coeff_48 i

end InternalCatalan

end

end

end OAI
