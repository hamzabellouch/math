import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalBounds
import OAI.Analysis.MatrixSigning.Matrices.DeterminantBounds

namespace OAI

section

namespace KS.W30

open scoped Rat

theorem integer_matrix_inverse_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) :
    ((A.map (fun z : ℤ => (z : ℚ)))⁻¹) i j =
      (A.adjugate i j : ℚ) / (A.det : ℚ) := by
  have hadj := (Int.castRingHom ℚ).map_adjugate A
  have hdet := (Int.castRingHom ℚ).map_det A
  change A.adjugate.map (fun z : ℤ => (z : ℚ)) =
    (A.map (fun z : ℤ => (z : ℚ))).adjugate at hadj
  change (A.det : ℚ) = (A.map (fun z : ℤ => (z : ℚ))).det at hdet
  rw [Matrix.inv_def, ← hdet, ← hadj]
  simp [Matrix.smul_apply, Ring.inverse_eq_inv, div_eq_mul_inv, mul_comm]

theorem integer_inverse_parts_size_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (b : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ b) (hdet : A.det ≠ 0)
    (i j : Fin n) :
    let q := ((A.map (fun z : ℤ => (z : ℚ)))⁻¹) i j
    Nat.size q.num.natAbs ≤ n * n + b * n + 1 ∧
      Nat.size q.den ≤ n * n + b * n + 1 := by
  dsimp only
  rw [integer_matrix_inverse_entry, ← Rat.divInt_eq_div]
  have hs : 2 ^ (n * n + b * n) < 2 ^ (n * n + b * n + 1) := by
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _)
  constructor
  · exact divInt_num_size_le _ _ hdet _
      (lt_of_le_of_lt (natAbs_adjugate_le_two_pow A b hA i j) hs)
  · exact divInt_den_size_le _ _ hdet _
      (lt_of_le_of_lt (natAbs_det_le_two_pow A b hA) hs)

theorem rational_matrix_inverse_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hdet : A.det ≠ 0) (i j : Fin n) :
    A⁻¹ i j = ((A.den : ℤ) * A.num.adjugate i j : ℤ) /. A.num.det := by
  have hD : (A.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr A.den_ne_zero
  let : Invertible (A.den : ℚ) := invertibleOfNonzero hD
  have hN : A.num.map (fun z : ℤ => (z : ℚ)) = (A.den : ℚ) • A := by
    ext k l
    exact cleared_matrix_entry A k l
  have hi : A⁻¹ = (A.den : ℚ) • (A.num.map (fun z : ℤ => (z : ℚ)))⁻¹ := by
    rw [hN, Matrix.inv_smul A (A.den : ℚ) (isUnit_iff_ne_zero.mpr hdet)]
    simp [smul_smul, invOf_eq_inv, hD]
  rw [hi, Matrix.smul_apply, smul_eq_mul, integer_matrix_inverse_entry]
  simp only [Rat.divInt_eq_div, Int.cast_mul, Int.cast_natCast]
  exact (mul_div_assoc _ _ _).symm

theorem cleared_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hdet : A.det ≠ 0) : A.num.det ≠ 0 := by
  have hD : (A.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr A.den_ne_zero
  have hN : A.num.map (fun z : ℤ => (z : ℚ)) = (A.den : ℚ) • A := by
    ext k l
    exact cleared_matrix_entry A k l
  intro hz
  have heq : ((A.den : ℚ) • A).det = 0 := by
    rw [← hN, ← Int.cast_det, hz, Int.cast_zero]
  have hz' : ((A.den : ℚ) ^ n) * A.det = 0 := by
    simpa only [Matrix.det_smul, Fintype.card_fin] using heq
  exact (mul_ne_zero (pow_ne_zero _ hD) hdet) hz'

theorem rational_inverse_parts_size_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (b : ℕ) (hnum : ∀ i j, (A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (A i j).den ≤ 2 ^ b) (hdet : A.det ≠ 0)
    (i j : Fin n) :
    let K := b * (n * n) + (n * n + (b * (n * n) + b) * n)
    Nat.size (A⁻¹ i j).num.natAbs ≤ K + 1 ∧
      Nat.size (A⁻¹ i j).den ≤ K + 1 := by
  let c := b * (n * n) + b
  let e := n * n + c * n
  let K := b * (n * n) + e
  have hN : ∀ k l, (A.num k l).natAbs ≤ 2 ^ c :=
    fun k l => cleared_num_le_two_pow A b hnum hden k l
  have hnum' : (((A.den : ℤ) * A.num.adjugate i j : ℤ)).natAbs ≤ 2 ^ K := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    calc
      A.den * (A.num.adjugate i j).natAbs ≤
          2 ^ (b * (n * n)) * 2 ^ e :=
        Nat.mul_le_mul (matrix_den_le_two_pow A b hden)
          (natAbs_adjugate_le_two_pow A.num c hN i j)
      _ = 2 ^ K := (pow_add 2 _ _).symm
  have hden' : A.num.det.natAbs ≤ 2 ^ K := by
    apply le_trans (natAbs_det_le_two_pow A.num c hN)
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left e _)
  have hs : 2 ^ K < 2 ^ (K + 1) := by
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _)
  change Nat.size (A⁻¹ i j).num.natAbs ≤ K + 1 ∧ Nat.size (A⁻¹ i j).den ≤ K + 1
  rw [rational_matrix_inverse_entry A hdet]
  exact ⟨divInt_num_size_le _ _ (cleared_det_ne_zero A hdet) _ (lt_of_le_of_lt hnum' hs),
    divInt_den_size_le _ _ (cleared_det_ne_zero A hdet) _ (lt_of_le_of_lt hden' hs)⟩

theorem rational_inverse_parts_size_le_fintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (b : ℕ)
    (hnum : ∀ i j, (A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (A i j).den ≤ 2 ^ b) (hdet : A.det ≠ 0) (i j : ι) :
    let n := Fintype.card ι
    let K := b * (n * n) + (n * n + (b * (n * n) + b) * n)
    Nat.size (A⁻¹ i j).num.natAbs ≤ K + 1 ∧
      Nat.size (A⁻¹ i j).den ≤ K + 1 := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let B := A.submatrix e.symm e.symm
  have hBnum : ∀ k l, (B k l).num.natAbs ≤ 2 ^ b := fun k l => hnum _ _
  have hBden : ∀ k l, (B k l).den ≤ 2 ^ b := fun k l => hden _ _
  have hBdet : B.det ≠ 0 := by
    simpa [B] using hdet
  have h := rational_inverse_parts_size_le B b hBnum hBden hBdet (e i) (e j)
  simpa [B, Matrix.inv_submatrix_equiv, Matrix.submatrix_apply] using h

end KS.W30

end

end OAI
