import OAI.Analysis.Quantum.DimensionTen.LowBasis

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

def C : Matrix (Fin 15) (Fin 20) ℚ := (d : ℚ)⁻¹ • Cnum.map (Int.castRingHom ℚ)

lemma normalize_border (B : Matrix (Fin 20) (Fin 20) ℤ) (i : Fin 15) (k : Fin 20)
    (h : ∀ m, B m k = Cnum i m) :
    ((d : ℚ)⁻¹ • B.map (Int.castRingHom ℚ)) *ᵥ eQ k = C i := by
  ext m
  simp only [eQ, Matrix.mulVec_single_one, Matrix.smul_apply, Matrix.map_apply,
    Matrix.col_apply, C, smul_eq_mul]
  rw [h m]

lemma E_sum (c : Fin 20 → ℚ) : E (∑ m, c m • low alpha m) = c := by
  ext k
  simp [map_sum, E_low, eQ, Pi.single_apply]

lemma high_shift_0 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 0 = t 2 * low t 10 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_0 : ∀ m : Fin 20, B2 m 10 = Cnum 0 m := by decide +kernel

lemma NB_border_0 : NB 2 *ᵥ eQ 10 = C 0 := by
  exact normalize_border B2 0 10 border_column_0

lemma high_relation_0 : high alpha 0 = ∑ m, C 0 m • low alpha m := by
  apply E_injective
  rw [high_shift_0, E_mul, rho_alpha, E_low, NB_border_0, E_sum]

lemma high_shift_1 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 1 = t 1 * low t 10 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]

lemma border_column_1 : ∀ m : Fin 20, B1 m 10 = Cnum 1 m := by decide +kernel

lemma NB_border_1 : NB 1 *ᵥ eQ 10 = C 1 := by
  exact normalize_border B1 1 10 border_column_1

lemma high_relation_1 : high alpha 1 = ∑ m, C 1 m • low alpha m := by
  apply E_injective
  rw [high_shift_1, E_mul, rho_alpha, E_low, NB_border_1, E_sum]

lemma high_shift_2 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 2 = t 1 * low t 11 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_2 : ∀ m : Fin 20, B1 m 11 = Cnum 2 m := by decide +kernel

lemma NB_border_2 : NB 1 *ᵥ eQ 11 = C 2 := by
  exact normalize_border B1 2 11 border_column_2

lemma high_relation_2 : high alpha 2 = ∑ m, C 2 m • low alpha m := by
  apply E_injective
  rw [high_shift_2, E_mul, rho_alpha, E_low, NB_border_2, E_sum]

lemma high_shift_3 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 3 = t 1 * low t 12 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_3 : ∀ m : Fin 20, B1 m 12 = Cnum 3 m := by decide +kernel

lemma NB_border_3 : NB 1 *ᵥ eQ 12 = C 3 := by
  exact normalize_border B1 3 12 border_column_3

lemma high_relation_3 : high alpha 3 = ∑ m, C 3 m • low alpha m := by
  apply E_injective
  rw [high_shift_3, E_mul, rho_alpha, E_low, NB_border_3, E_sum]

lemma high_shift_4 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 4 = t 1 * low t 13 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_4 : ∀ m : Fin 20, B1 m 13 = Cnum 4 m := by decide +kernel

lemma NB_border_4 : NB 1 *ᵥ eQ 13 = C 4 := by
  exact normalize_border B1 4 13 border_column_4

lemma high_relation_4 : high alpha 4 = ∑ m, C 4 m • low alpha m := by
  apply E_injective
  rw [high_shift_4, E_mul, rho_alpha, E_low, NB_border_4, E_sum]

lemma high_shift_5 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 5 = t 0 * low t 10 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]

lemma border_column_5 : ∀ m : Fin 20, B0 m 10 = Cnum 5 m := by decide +kernel

lemma NB_border_5 : NB 0 *ᵥ eQ 10 = C 5 := by
  exact normalize_border B0 5 10 border_column_5

lemma high_relation_5 : high alpha 5 = ∑ m, C 5 m • low alpha m := by
  apply E_injective
  rw [high_shift_5, E_mul, rho_alpha, E_low, NB_border_5, E_sum]

lemma high_shift_6 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 6 = t 0 * low t 11 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]

lemma border_column_6 : ∀ m : Fin 20, B0 m 11 = Cnum 6 m := by decide +kernel

lemma NB_border_6 : NB 0 *ᵥ eQ 11 = C 6 := by
  exact normalize_border B0 6 11 border_column_6

lemma high_relation_6 : high alpha 6 = ∑ m, C 6 m • low alpha m := by
  apply E_injective
  rw [high_shift_6, E_mul, rho_alpha, E_low, NB_border_6, E_sum]

lemma high_shift_7 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 7 = t 0 * low t 12 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]

lemma border_column_7 : ∀ m : Fin 20, B0 m 12 = Cnum 7 m := by decide +kernel

lemma NB_border_7 : NB 0 *ᵥ eQ 12 = C 7 := by
  exact normalize_border B0 7 12 border_column_7

lemma high_relation_7 : high alpha 7 = ∑ m, C 7 m • low alpha m := by
  apply E_injective
  rw [high_shift_7, E_mul, rho_alpha, E_low, NB_border_7, E_sum]

lemma high_shift_8 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 8 = t 0 * low t 13 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]

lemma border_column_8 : ∀ m : Fin 20, B0 m 13 = Cnum 8 m := by decide +kernel

lemma NB_border_8 : NB 0 *ᵥ eQ 13 = C 8 := by
  exact normalize_border B0 8 13 border_column_8

lemma high_relation_8 : high alpha 8 = ∑ m, C 8 m • low alpha m := by
  apply E_injective
  rw [high_shift_8, E_mul, rho_alpha, E_low, NB_border_8, E_sum]

lemma high_shift_9 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 9 = t 0 * low t 14 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_9 : ∀ m : Fin 20, B0 m 14 = Cnum 9 m := by decide +kernel

lemma NB_border_9 : NB 0 *ᵥ eQ 14 = C 9 := by
  exact normalize_border B0 9 14 border_column_9

lemma high_relation_9 : high alpha 9 = ∑ m, C 9 m • low alpha m := by
  apply E_injective
  rw [high_shift_9, E_mul, rho_alpha, E_low, NB_border_9, E_sum]

lemma high_shift_10 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 10 = t 0 * low t 15 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_10 : ∀ m : Fin 20, B0 m 15 = Cnum 10 m := by decide +kernel

lemma NB_border_10 : NB 0 *ᵥ eQ 15 = C 10 := by
  exact normalize_border B0 10 15 border_column_10

lemma high_relation_10 : high alpha 10 = ∑ m, C 10 m • low alpha m := by
  apply E_injective
  rw [high_shift_10, E_mul, rho_alpha, E_low, NB_border_10, E_sum]

lemma high_shift_11 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 11 = t 0 * low t 16 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_11 : ∀ m : Fin 20, B0 m 16 = Cnum 11 m := by decide +kernel

lemma NB_border_11 : NB 0 *ᵥ eQ 16 = C 11 := by
  exact normalize_border B0 11 16 border_column_11

lemma high_relation_11 : high alpha 11 = ∑ m, C 11 m • low alpha m := by
  apply E_injective
  rw [high_shift_11, E_mul, rho_alpha, E_low, NB_border_11, E_sum]

lemma high_shift_12 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 12 = t 0 * low t 17 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_12 : ∀ m : Fin 20, B0 m 17 = Cnum 12 m := by decide +kernel

lemma NB_border_12 : NB 0 *ᵥ eQ 17 = C 12 := by
  exact normalize_border B0 12 17 border_column_12

lemma high_relation_12 : high alpha 12 = ∑ m, C 12 m • low alpha m := by
  apply E_injective
  rw [high_shift_12, E_mul, rho_alpha, E_low, NB_border_12, E_sum]

lemma high_shift_13 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 13 = t 0 * low t 18 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_13 : ∀ m : Fin 20, B0 m 18 = Cnum 13 m := by decide +kernel

lemma NB_border_13 : NB 0 *ᵥ eQ 18 = C 13 := by
  exact normalize_border B0 13 18 border_column_13

lemma high_relation_13 : high alpha 13 = ∑ m, C 13 m • low alpha m := by
  apply E_injective
  rw [high_shift_13, E_mul, rho_alpha, E_low, NB_border_13, E_sum]

lemma high_shift_14 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    high t 14 = t 0 * low t 19 := by
  simp [high, low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma border_column_14 : ∀ m : Fin 20, B0 m 19 = Cnum 14 m := by decide +kernel

lemma NB_border_14 : NB 0 *ᵥ eQ 19 = C 14 := by
  exact normalize_border B0 14 19 border_column_14

lemma high_relation_14 : high alpha 14 = ∑ m, C 14 m • low alpha m := by
  apply E_injective
  rw [high_shift_14, E_mul, rho_alpha, E_low, NB_border_14, E_sum]

lemma high_relation (i : Fin 15) : high alpha i = ∑ m, C i m • low alpha m := by
  fin_cases i
  · exact high_relation_0
  · exact high_relation_1
  · exact high_relation_2
  · exact high_relation_3
  · exact high_relation_4
  · exact high_relation_5
  · exact high_relation_6
  · exact high_relation_7
  · exact high_relation_8
  · exact high_relation_9
  · exact high_relation_10
  · exact high_relation_11
  · exact high_relation_12
  · exact high_relation_13
  · exact high_relation_14

end DimensionTen.Border

end
end

end OAI
