import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotHistoryRun

namespace OAI

section

namespace KS.W07

open Matrix

theorem selectedSchur_smul {N k t : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N) (r : Fin t → Fin N)
    (c : ℚ) (hc : c ≠ 0) (hp : (M.submatrix p p).det ≠ 0) :
    selectedSchur (c • M) p r = c • selectedSchur M p r := by
  exact KS.W30.schur_smul (M.submatrix p p) (M.submatrix p r)
    (M.submatrix r p) (M.submatrix r r) c hc hp

theorem original_num_cast {dimension : ℕ} (M : Matrix (Fin dimension) (Fin dimension) ℚ) :
    M.num.map (fun z : ℤ => (z : ℚ)) = (M.den : ℚ) • M := by
  ext i j
  exact KS.W30.cleared_matrix_entry M i j

theorem original_num_selected_det_ne_zero {N k : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N)
    (hp : (M.submatrix p p).det ≠ 0) : (M.num.submatrix p p).det ≠ 0 := by
  have heq : (M.num.submatrix p p).map (fun z : ℤ => (z : ℚ)) =
      (M.den : ℚ) • M.submatrix p p := by
    ext i j
    exact KS.W30.cleared_matrix_entry M (p i) (p j)
  have hd : ((M.num.submatrix p p).det : ℚ) =
      (M.den : ℚ) ^ k * (M.submatrix p p).det := by
    rw [Int.cast_det, heq, Matrix.det_smul, Fintype.card_fin]
  have hn : (M.den : ℚ) ^ k * (M.submatrix p p).det ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr M.den_ne_zero)) hp
  intro hz
  apply hn
  rw [← hd, hz, Int.cast_zero]

theorem selectedSchur_entry_cleared_ratio {N k t : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N) (r : Fin t → Fin N)
    (hp : (M.submatrix p p).det ≠ 0) (i j : Fin t) :
    selectedSchur M p r i j =
      Rat.divInt (M.num.submatrix (Fin.snoc p (r i)) (Fin.snoc p (r j))).det
        ((M.den : ℤ) * (M.num.submatrix p p).det) := by
  let Z := M.num.map (fun z : ℤ => (z : ℚ))
  have hz : (M.num.submatrix p p).det ≠ 0 := original_num_selected_det_ne_zero M p hp
  have hzp : (Z.submatrix p p).det ≠ 0 := by
    change ((M.num.submatrix p p).map (fun z : ℤ => (z : ℚ))).det ≠ 0
    rw [← Int.cast_det]
    exact_mod_cast hz
  have hs : selectedSchur Z p r = (M.den : ℚ) • selectedSchur M p r := by
    rw [show Z = (M.den : ℚ) • M from original_num_cast M]
    exact selectedSchur_smul M p r _ (Nat.cast_ne_zero.mpr M.den_ne_zero) hp
  have he := congrFun (congrFun hs i) j
  rw [selectedSchur_entry_minor_ratio Z p r hzp i j] at he
  have hd : (Z.submatrix p p).det = ((M.num.submatrix p p).det : ℚ) := by
    exact (Int.cast_det (M.num.submatrix p p)).symm
  have hb : (Z.submatrix (Fin.snoc p (r i)) (Fin.snoc p (r j))).det =
      ((M.num.submatrix (Fin.snoc p (r i)) (Fin.snoc p (r j))).det : ℚ) := by
    exact (Int.cast_det _).symm
  rw [hd, hb] at he
  have hq : ((M.num.submatrix p p).det : ℚ) ≠ 0 := by exact_mod_cast hz
  have hc : (M.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr M.den_ne_zero
  have hcross := (div_eq_iff hq).mp he
  rw [Rat.divInt_eq_div, Int.cast_mul, Int.cast_natCast]
  apply (eq_div_iff (mul_ne_zero hc hq)).mpr
  simpa only [Matrix.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hcross.symm

theorem PivotTrace.entry_parts_size_le {N k t : ℕ}
    {M : Matrix (Fin N) (Fin N) ℚ} {p : Fin k → Fin N} {r : Fin t → Fin N}
    {S : Matrix (Fin t) (Fin t) ℚ} (h : PivotTrace M p r S)
    (b : ℕ) (hnum : ∀ i j, (M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (M i j).den ≤ 2 ^ b) (i j : Fin t) :
    Nat.size (S i j).num.natAbs ≤ KS.W30.inverseBitBound N b ∧
      Nat.size (S i j).den ≤ KS.W30.inverseBitBound N b := by
  obtain ⟨hp, hs⟩ := h.originalSchur
  have hdim := h.size_bound
  have hi := i.isLt
  have hk : k ≤ N := by omega
  have hk1 : k + 1 ≤ N := by omega
  rw [hs, selectedSchur_entry_cleared_ratio M p r hp i j]
  exact KS.W30.cleared_minor_ratio_parts_size_le M b hnum hden
    (Fin.snoc p (r i)) (Fin.snoc p (r j)) p p hk1 hk
    (original_num_selected_det_ne_zero M p hp)

theorem ldlHistory_entry_parts_size_le {N : ℕ} (A : DenseRatMatrix N)
    (hA : ((DenseRatMatrix.decode A).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (b : ℕ) (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2 ^ b)
    (steps : ℕ) (i j : Fin (ldlHistory A steps).remainingCount) :
    Nat.size (DenseRatMatrix.decode (ldlHistory A steps).matrix i j).num.natAbs ≤
        KS.W30.inverseBitBound N b ∧
      Nat.size (DenseRatMatrix.decode (ldlHistory A steps).matrix i j).den ≤
        KS.W30.inverseBitBound N b := by
  exact (ldlHistory_valid A hA steps : PivotTrace (DenseRatMatrix.decode A)
    (ldlHistory A steps).selected (ldlHistory A steps).remaining
    (DenseRatMatrix.decode (ldlHistory A steps).matrix)).entry_parts_size_le b hnum hden i j

end KS.W07

end

end OAI
