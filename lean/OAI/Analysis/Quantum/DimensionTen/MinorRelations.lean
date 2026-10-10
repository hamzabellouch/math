import OAI.Analysis.Quantum.DimensionTen.MinorData

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma minors_eq {R : Type*} [CommRing R] (x : Fin 4 → R) :
    minor x = D.map (Int.castRingHom R) *ᵥ homogeneousLow x +
      H.map (Int.castRingHom R) *ᵥ high (fun j => x j.succ) := by
  funext i
  fin_cases i
  · exact minors_row_0 x
  · exact minors_row_1 x
  · exact minors_row_2 x
  · exact minors_row_3 x
  · exact minors_row_4 x
  · exact minors_row_5 x
  · exact minors_row_6 x
  · exact minors_row_7 x
  · exact minors_row_8 x
  · exact minors_row_9 x
  · exact minors_row_10 x
  · exact minors_row_11 x
  · exact minors_row_12 x
  · exact minors_row_13 x
  · exact minors_row_14 x

lemma detH_ne_zero {R : Type*} [Field R] [CharZero R] : (detH : R) ≠ 0 := by
  norm_num [detH, PencilAlgebra.denominator]

lemma H_left_inverse {R : Type*} [CommRing R] :
    adjH.map (Int.castRingHom R) * H.map (Int.castRingHom R) =
      (detH : R) • (1 : Matrix (Fin 15) (Fin 15) R) := by
  have h := congrArg (Int.castRingHom R).mapMatrix inverse
  rw [Int.cast_smul_eq_zsmul]
  simpa only [map_mul, map_zsmul, map_one, RingHom.mapMatrix_apply] using h

lemma H_mulVec_injective {R : Type*} [Field R] [CharZero R] :
    Function.Injective (fun v => H.map (Int.castRingHom R) *ᵥ v) := by
  intro u v h
  have hh := congrArg (fun w => adjH.map (Int.castRingHom R) *ᵥ w) h
  simp only [Matrix.mulVec_mulVec, H_left_inverse, Matrix.smul_mulVec, Matrix.one_mulVec] at hh
  have hhh := congrArg (fun w => (detH : R)⁻¹ • w) hh
  simpa only [smul_smul, inv_mul_cancel₀ (detH_ne_zero (R := R)), one_smul] using hhh

lemma low_at_infinity {R : Type*} [CommRing R] (x : Fin 4 → R) (hx : x 0 = 0) :
    homogeneousLow x = 0 := by
  ext i
  fin_cases i <;> simp [homogeneousLow, monExps, hx, Fin.sum_univ_succ]

lemma high_zero {R : Type*} [Field R] (t : Fin 3 → R) (h : high t = 0) : t = 0 := by
  have h0 := congrFun h 14
  have h1 := congrFun h 4
  have h2 := congrFun h 0
  have ht0 : t 0 ^ 4 = 0 := by simpa [high, mon, monExps, Fin.prod_univ_succ] using h0
  have ht1 : t 1 ^ 4 = 0 := by simpa [high, mon, monExps, Fin.prod_univ_succ] using h1
  have ht2 : t 2 ^ 4 = 0 := by simpa [high, mon, monExps, Fin.prod_univ_succ] using h2
  ext i
  fin_cases i
  · exact eq_zero_of_pow_eq_zero ht0
  · exact eq_zero_of_pow_eq_zero ht1
  · exact eq_zero_of_pow_eq_zero ht2

lemma no_infinity {R : Type*} [Field R] [CharZero R] (x : Fin 4 → R)
    (hx : x ≠ 0) (hm : minor x = 0) : x 0 ≠ 0 := by
  intro h0
  rw [minors_eq, low_at_infinity x h0, Matrix.mulVec_zero, zero_add] at hm
  have hh : high (fun j => x j.succ) = 0 :=
    H_mulVec_injective (hm.trans (Matrix.mulVec_zero _).symm)
  have ht := high_zero _ hh
  apply hx
  ext i
  refine Fin.cases h0 (fun j => congrFun ht j) i

lemma minor_zero_of_rank_lt {R : Type*} [Field R] (x : Fin 4 → R)
    (h : (pencilR x).rank < 4) : minor x = 0 := by
  ext i
  by_contra hi
  have hr := Matrix.rank_of_det_ne_zero (show ((pencilR x).submatrix (rowChoices i) id).det ≠ 0 from hi)
  have hs := Matrix.rank_submatrix_le (pencilR x) (rowChoices i) id
  simp only [Fintype.card_fin] at hr
  omega

lemma homogeneousLow_chart {R : Type*} [CommRing R] (t : Fin 3 → R) :
    homogeneousLow (Fin.cons 1 t) = low t := by
  ext i
  simp [homogeneousLow]

end DimensionTen.Border

end
end

end OAI
