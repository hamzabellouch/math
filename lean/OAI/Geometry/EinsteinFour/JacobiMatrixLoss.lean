import OAI.Geometry.EinsteinFour.Jacobi
import OAI.Geometry.EinsteinFour.ReferenceCompression
import Mathlib.Analysis.Matrix.Order

namespace OAI

/-! The scalar determinant deficit applied to the actual symmetric matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

private theorem trace_unitary_conj (U : Matrix.unitaryGroup (Fin 3) ℝ) (A : NormalMatrix) :
    (Unitary.conjStarAlgAut ℝ NormalMatrix U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

private theorem det_unitary_conj (U : Matrix.unitaryGroup (Fin 3) ℝ) (A : NormalMatrix) :
    (Unitary.conjStarAlgAut ℝ NormalMatrix U A).det = A.det := by
  have hU := congrArg Matrix.det (Unitary.coe_star_mul_self U)
  simp only [Matrix.det_mul, Matrix.det_one] at hU
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
  calc
    _ = ((star U : NormalMatrix).det * (U : NormalMatrix).det) * A.det := by ring
    _ = A.det := by rw [hU, one_mul]

private theorem posSemidef_unitary_conj (U : Matrix.unitaryGroup (Fin 3) ℝ)
    {A : NormalMatrix} (hA : A.PosSemidef) :
    (Unitary.conjStarAlgAut ℝ NormalMatrix U A).PosSemidef := by
  have h := hA.conjTranspose_mul_mul_same (star (U : NormalMatrix))
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using h

private theorem frobenius_sq_eq_trace_square {A : NormalMatrix} (hA : A.IsHermitian) :
    ‖A‖ ^ 2 = (A * A).trace := by
  have hs (i j : Fin 3) : A j i = A i j := by
    have h := congrFun (congrFun hA.eq i) j
    exact h
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [Real.sq_sqrt (by positivity)]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs, pow_two]

/-- The concrete Frobenius norm is the sum of the three eigenvalue squares. -/
theorem frobenius_sq_eq_sum_eigenvalues {A : NormalMatrix} (hA : A.IsHermitian) :
    ‖A‖ ^ 2 = ∑ i, (hA.eigenvalues i) ^ 2 := by
  let φ := Unitary.conjStarAlgAut ℝ NormalMatrix (star hA.eigenvectorUnitary)
  have hd : φ A = diagonal hA.eigenvalues := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [frobenius_sq_eq_trace_square hA]
  calc
    (A * A).trace = (φ (A * A)).trace :=
      (trace_unitary_conj (star hA.eigenvectorUnitary) (A * A)).symm
    _ = (diagonal hA.eigenvalues * diagonal hA.eigenvalues).trace := by rw [map_mul, hd]
    _ = ∑ i, hA.eigenvalues i ^ 2 := by simp [Matrix.diagonal_mul_diagonal, pow_two]

/-- Matrix form of the preconjugate determinant loss. The two semidefinite
hypotheses are exactly the lower curvature bound and the first-mode compression. -/
theorem matrix_preconjugate_loss {A : NormalMatrix} {β : ℝ} (hA : A.IsHermitian)
    (hβ : 0 ≤ β) (htrace : A.trace = 0)
    (hlower : (A + 1).PosSemidef) (hupper : (1 - β • A).PosSemidef) :
    (1 - β • A).det ≤ 1 - lossFactor β / 6 * ‖A‖ ^ 2 := by
  let φ := Unitary.conjStarAlgAut ℝ NormalMatrix (star hA.eigenvectorUnitary)
  let e := hA.eigenvalues
  have hd : φ A = diagonal e := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hlo := posSemidef_unitary_conj (star hA.eigenvectorUnitary) hlower
  have hup := posSemidef_unitary_conj (star hA.eigenvectorUnitary) hupper
  change (φ (A + 1)).PosSemidef at hlo
  change (φ (1 - β • A)).PosSemidef at hup
  have hdiaglo : φ (A + 1) = diagonal (fun i => e i + 1) := by
    rw [map_add, map_one, hd]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hdiagup : φ (1 - β • A) = diagonal (fun i => 1 - β * e i) := by
    rw [map_sub, map_one, map_smul, hd]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.smul_apply, smul_eq_mul, hij]
  rw [hdiaglo, Matrix.posSemidef_diagonal_iff] at hlo
  rw [hdiagup, Matrix.posSemidef_diagonal_iff] at hup
  have htr : e 0 + e 1 + e 2 = 0 := by
    have h := hA.trace_eq_sum_eigenvalues
    simpa [Fin.sum_univ_succ, htrace, e, add_assoc] using h.symm
  have hn : ‖A‖ ^ 2 = e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2 := by
    simpa [Fin.sum_univ_succ, e, add_assoc] using frobenius_sq_eq_sum_eigenvalues hA
  have hdet : (1 - β • A).det = (1 - β * e 0) * (1 - β * e 1) * (1 - β * e 2) := by
    rw [← det_unitary_conj (star hA.eigenvectorUnitary) (1 - β • A)]
    change (φ (1 - β • A)).det = _
    rw [hdiagup, Matrix.det_diagonal]
    simp [Fin.prod_univ_succ, mul_assoc]
  have hloss := preconjugate_loss hβ htr (by linarith [hlo 0])
    (by linarith [hlo 1]) (by linarith [hlo 2]) (by linarith [hup 0])
    (by linarith [hup 1]) (by linarith [hup 2])
  rw [hn, hdet]
  unfold loss at hloss
  linarith

/-- The positive curvature lower bound and trace normalization also control
the postconjugate branch, where radial density is set to zero. -/
theorem matrix_postconjugate_loss {A : NormalMatrix} (hA : A.IsHermitian)
    (β : ℝ) (htrace : A.trace = 0) (hlower : (A + 1).PosSemidef) :
    lossFactor β / 6 * ‖A‖ ^ 2 ≤ 1 := by
  let φ := Unitary.conjStarAlgAut ℝ NormalMatrix (star hA.eigenvectorUnitary)
  let e := hA.eigenvalues
  have hd : φ A = diagonal e := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hlo := posSemidef_unitary_conj (star hA.eigenvectorUnitary) hlower
  change (φ (A + 1)).PosSemidef at hlo
  have hdiaglo : φ (A + 1) = diagonal (fun i => e i + 1) := by
    rw [map_add, map_one, hd]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hdiaglo, Matrix.posSemidef_diagonal_iff] at hlo
  have htr : e 0 + e 1 + e 2 = 0 := by
    have h := hA.trace_eq_sum_eigenvalues
    simpa [Fin.sum_univ_succ, htrace, e, add_assoc] using h.symm
  have hn : ‖A‖ ^ 2 = e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2 := by
    simpa [Fin.sum_univ_succ, e, add_assoc] using frobenius_sq_eq_sum_eigenvalues hA
  rw [hn]
  exact postconjugate_loss htr
    ⟨by linarith [hlo 0], by linarith [hlo 1, hlo 2]⟩
    ⟨by linarith [hlo 1], by linarith [hlo 0, hlo 2]⟩
    ⟨by linarith [hlo 2], by linarith [hlo 0, hlo 1]⟩

end

end PositiveEinsteinFour.Jacobi

end OAI
