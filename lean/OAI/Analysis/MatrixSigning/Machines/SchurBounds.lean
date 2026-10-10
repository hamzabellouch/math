import Mathlib
import OAI.Analysis.MatrixSigning.Machines.InverseHeight

namespace OAI

section

namespace KS.W30

open scoped Rat

theorem schur_scalar_det_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (B : Matrix ι Unit ℚ) (C : Matrix Unit ι ℚ)
    (D : Matrix Unit Unit ℚ) (hdet : A.det ≠ 0) :
    (D - C * A⁻¹ * B) () () = (Matrix.fromBlocks A B C D).det / A.det := by
  let : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hdet)
  have h := Matrix.det_fromBlocks₁₁ A B C D
  rw [Matrix.invOf_eq_nonsing_inv] at h
  rw [Matrix.det_unique (D - C * A⁻¹ * B)] at h
  apply (eq_div_iff hdet).mpr
  simpa [mul_comm] using h.symm

theorem integer_schur_scalar_det_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (B : Matrix ι Unit ℤ) (C : Matrix Unit ι ℤ)
    (D : Matrix Unit Unit ℤ) (hdet : A.det ≠ 0) :
    ((D.map (fun z : ℤ => (z : ℚ))) -
      (C.map (fun z : ℤ => (z : ℚ))) * (A.map (fun z : ℤ => (z : ℚ)))⁻¹ *
        (B.map (fun z : ℤ => (z : ℚ)))) () () =
      (Matrix.fromBlocks A B C D).det /. A.det := by
  have hdet' : (A.map (fun z : ℤ => (z : ℚ))).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast hdet
  rw [schur_scalar_det_ratio _ _ _ _ hdet', Rat.divInt_eq_div]
  congr 1
  · rw [Int.cast_det]
    congr 1
    ext i j
    cases i <;> cases j <;> rfl
  · exact (Int.cast_det A).symm

theorem natAbs_det_le_two_pow_fintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (b : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ b) :
    A.det.natAbs ≤ 2 ^ (Fintype.card ι * Fintype.card ι + b * Fintype.card ι) := by
  let e := (Fintype.equivFin ι).symm
  have h := natAbs_det_le_two_pow (A.submatrix e e) b (fun i j => hA _ _)
  simpa using h

theorem integer_det_ratio_parts_size_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℤ) (M : Matrix κ κ ℤ) (b : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ b)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ b) (hdet : A.det ≠ 0) :
    Nat.size (M.det /. A.det).num.natAbs ≤
      Fintype.card κ * Fintype.card κ + b * Fintype.card κ + 1 ∧
    Nat.size (M.det /. A.det).den ≤
      Fintype.card ι * Fintype.card ι + b * Fintype.card ι + 1 := by
  have hp (k : ℕ) : 2 ^ k < 2 ^ (k + 1) := by
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _)
  constructor
  · exact divInt_num_size_le _ _ hdet _
      (lt_of_le_of_lt (natAbs_det_le_two_pow_fintype M b hM) (hp _))
  · exact divInt_den_size_le _ _ hdet _
      (lt_of_le_of_lt (natAbs_det_le_two_pow_fintype A b hA) (hp _))

theorem minor_natAbs_le_two_pow {n k : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (f g : Fin k → Fin n) (b : ℕ) (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ b)
    (hk : k ≤ n) :
    (M.submatrix f g).det.natAbs ≤ 2 ^ (n * n + b * n) := by
  apply le_trans (natAbs_det_le_two_pow (M.submatrix f g) b (fun i j => hM _ _))
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  exact Nat.add_le_add (Nat.mul_le_mul hk hk) (Nat.mul_le_mul_left b hk)

theorem minor_ratio_parts_size_le {n k l : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (f g : Fin k → Fin n) (u v : Fin l → Fin n) (b : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ b) (hk : k ≤ n) (hl : l ≤ n)
    (hden : (M.submatrix u v).det ≠ 0) :
    let q := (M.submatrix f g).det /. (M.submatrix u v).det
    Nat.size q.num.natAbs ≤ n * n + b * n + 1 ∧
      Nat.size q.den ≤ n * n + b * n + 1 := by
  have hp : 2 ^ (n * n + b * n) < 2 ^ (n * n + b * n + 1) := by
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _)
  exact ⟨divInt_num_size_le _ _ hden _
      (lt_of_le_of_lt (minor_natAbs_le_two_pow M f g b hM hk) hp),
    divInt_den_size_le _ _ hden _
      (lt_of_le_of_lt (minor_natAbs_le_two_pow M u v b hM hl) hp)⟩

theorem scaled_minor_ratio_parts_size_le {n k l : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) (D b d : ℕ) (hD : D ≠ 0) (hDb : D ≤ 2 ^ d)
    (f g : Fin k → Fin n) (u v : Fin l → Fin n)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ b) (hk : k ≤ n) (hl : l ≤ n)
    (hden : (M.submatrix u v).det ≠ 0) :
    let q := (M.submatrix f g).det /. ((D : ℤ) * (M.submatrix u v).det)
    Nat.size q.num.natAbs ≤ d + (n * n + b * n) + 1 ∧
      Nat.size q.den ≤ d + (n * n + b * n) + 1 := by
  let e := n * n + b * n
  have hn := minor_natAbs_le_two_pow M f g b hM hk
  have hd : ((D : ℤ) * (M.submatrix u v).det).natAbs ≤ 2 ^ (d + e) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, pow_add]
    exact Nat.mul_le_mul hDb (minor_natAbs_le_two_pow M u v b hM hl)
  have hh : ((D : ℤ) * (M.submatrix u v).det) ≠ 0 :=
    mul_ne_zero (Int.natCast_ne_zero.mpr hD) hden
  have hp : 2 ^ (d + e) < 2 ^ (d + e + 1) := by
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _)
  have hn' : (M.submatrix f g).det.natAbs < 2 ^ (d + e + 1) := by
    apply lt_of_le_of_lt hn
    exact lt_of_le_of_lt
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left e d)) hp
  exact ⟨divInt_num_size_le _ _ hh _ hn',
    divInt_den_size_le _ _ hh _ (lt_of_le_of_lt hd hp)⟩

theorem cleared_minor_ratio_parts_size_le {n k l : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (b : ℕ)
    (hnum : ∀ i j, (A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (A i j).den ≤ 2 ^ b)
    (f g : Fin k → Fin n) (u v : Fin l → Fin n) (hk : k ≤ n) (hl : l ≤ n)
    (hdet : (A.num.submatrix u v).det ≠ 0) :
    let q := (A.num.submatrix f g).det /.
      ((A.den : ℤ) * (A.num.submatrix u v).det)
    Nat.size q.num.natAbs ≤ inverseBitBound n b ∧
      Nat.size q.den ≤ inverseBitBound n b := by
  exact scaled_minor_ratio_parts_size_le A.num A.den (b * (n * n) + b) (b * (n * n))
    A.den_ne_zero (matrix_den_le_two_pow A b hden) f g u v
    (fun i j => cleared_num_le_two_pow A b hnum hden i j) hk hl hdet

theorem schur_smul {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℚ) (B : Matrix ι κ ℚ) (C : Matrix κ ι ℚ) (D : Matrix κ κ ℚ)
    (c : ℚ) (hc : c ≠ 0) (hA : A.det ≠ 0) :
    c • D - (c • C) * (c • A)⁻¹ * (c • B) = c • (D - C * A⁻¹ * B) := by
  let : Invertible c := invertibleOfNonzero hc
  rw [Matrix.inv_smul A c (isUnit_iff_ne_zero.mpr hA)]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, invOf_eq_inv, hc, smul_sub]

end KS.W30

end

end OAI
