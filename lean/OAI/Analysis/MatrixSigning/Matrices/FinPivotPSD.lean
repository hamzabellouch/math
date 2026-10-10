import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.FinPivot
import OAI.Analysis.MatrixSigning.Matrices.PivotPSD

namespace OAI

section

namespace KS.W07

theorem fin_psd_of_schurTail {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm)
    (ha : 0 < M 0 0)
    (hS : ((KS.W17.schurTail M).map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  apply (Matrix.posSemidef_submatrix_equiv (pivotIndexEquiv n)).mp
  change ((M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n)).map
    (fun q : ℚ => (q : ℝ))).PosSemidef
  rw [fin_pivotBlock M hM, rat_pivotBlock_cast]
  apply (pivotBlock_posSemidef_iff (by exact_mod_cast ha) _ _).mpr
  rw [← rat_pivotSchur_cast, fin_pivotSchur M hM]
  exact hS

theorem fin_psd_of_zero_pivot_tail {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm)
    (ha : M 0 0 = 0) (hrow : ∀ j : Fin n, M 0 j.succ = 0)
    (hD : ((KS.W17.trailingMatrix M).map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  apply (Matrix.posSemidef_submatrix_equiv (pivotIndexEquiv n)).mp
  change ((M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n)).map
    (fun q : ℚ => (q : ℝ))).PosSemidef
  rw [fin_pivotBlock M hM, rat_pivotBlock_cast]
  simp only [ha, hrow, Rat.cast_zero]
  exact zero_pivotBlock_posSemidef _ hD

theorem rational_isSymm_of_cast_posSemidef {n : Type*} [Fintype n]
    {M : Matrix n n ℚ} (hM : (M.map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    M.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  apply Rat.cast_injective (α := ℝ)
  simpa using hM.isHermitian.apply i j

theorem fin_schurTail_posSemidef {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hM : (M.map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    ((KS.W17.schurTail M).map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  by_cases hz : M 0 0 = 0
  · have hs : KS.W17.schurTail M = KS.W17.trailingMatrix M := by
      ext i j
      simp [KS.W17.schurTail, KS.W17.trailingMatrix, hz]
    rw [hs]
    exact hM.submatrix Fin.succ
  · have hsym := rational_isSymm_of_cast_posSemidef hM
    have ha0 : 0 ≤ M 0 0 := by
      have h := hM.diag_nonneg (i := (0 : Fin (n + 1)))
      simp only [Matrix.map_apply] at h
      exact_mod_cast h
    have ha : (0 : ℝ) < (M 0 0 : ℝ) := by
      exact_mod_cast (lt_of_le_of_ne ha0 (Ne.symm hz))
    have hsub := hM.submatrix (pivotIndexEquiv n)
    change ((M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n)).map
      (fun q : ℚ => (q : ℝ))).PosSemidef at hsub
    rw [fin_pivotBlock M hsym, rat_pivotBlock_cast] at hsub
    have h := pivotSchur_posSemidef ha _ _ hsub
    rw [← rat_pivotSchur_cast, fin_pivotSchur M hsym] at h
    exact h

end KS.W07

end

end OAI
