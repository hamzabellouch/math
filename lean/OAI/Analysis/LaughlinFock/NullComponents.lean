import Mathlib
import OAI.Analysis.LaughlinFock.ThreeSpectrum

namespace OAI

/-! Null Components. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

theorem gramShift_zero (Q : ℕ) : gramShift Q 0 = -1 := by
  simp [gramShift, fallingRatio]

theorem gramShift_one {Q : ℕ} (hQ : 2 ≤ Q) : gramShift Q 1 = -1 := by
  have hq : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have h0 : (Q : ℝ) ≠ 0 := by linarith
  have h1 : 2 * (Q : ℝ) - 2 ≠ 0 := by linarith
  unfold gramShift
  rw [fallingRatio_succ (z:=0) hQ (by omega)]
  norm_num only [Nat.cast_one, Nat.cast_zero, pow_one, fallingRatio,
    Nat.descFactorial_zero, div_one, sub_zero, mul_one]
  field_simp (disch := linarith)

theorem gramShift_three {Q : ℕ} (hQ : 3 ≤ Q) : gramShift Q 3 = -1 := by
  have hq : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
  have h0 : (Q : ℝ) ≠ 0 := by linarith
  have h1 : 2 * (Q : ℝ) - 2 ≠ 0 := by linarith
  have h2 : 2 * (Q : ℝ) - 2 - 1 ≠ 0 := by linarith
  have h3 : 2 * (Q : ℝ) - 2 - 2 ≠ 0 := by linarith
  unfold gramShift
  rw [fallingRatio_succ (z:=2) (by omega) (by omega),
    fallingRatio_succ (z:=1) (by omega) (by omega),
    fallingRatio_succ (z:=0) (by omega) (by omega)]
  norm_num only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    fallingRatio, Nat.descFactorial_zero, div_one, sub_zero, mul_one]
  field_simp (disch := linarith)
  ring

 

theorem threeWedgeMatrix_null_column {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hnull : z=0 ∨ z=1 ∨ z=3) (k : ℕ) :
    threeWedgeMatrix Q *ᵥ threeCoupledColumn Q z k = 0 := by
  have hshift : gramShift Q z = -1 := by
    rcases hnull with rfl | rfl | rfl
    · exact gramShift_zero Q
    · exact gramShift_one hQ
    · exact gramShift_three hz
  apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).mp
  rw [threeWedgeMatrix_gram_eigenvector hQ hz k, hshift]
  simp

 

theorem threeWedgeMatrix_null_projection {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hnull : z=0 ∨ z=1 ∨ z=3) :
    threeWedgeMatrix Q * threeSpinProjection Q z = 0 := by
  classical
  have hn : threeWedgeMatrix Q * threeCouplingMatrix Q *
      Matrix.diagonal (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=z then (1:ℂ) else 0) = 0 := by
    ext S c
    rw [Matrix.mul_diagonal]
    split_ifs with hc
    · rw [mul_one]
      change (threeWedgeMatrix Q *ᵥ threeCoupledColumn Q c.1.val c.2.val) S = 0
      simpa only [hc, Pi.zero_apply] using congrArg (fun v => v S)
        (threeWedgeMatrix_null_column hQ (show c.1.val ≤ Q by omega)
          (by simpa only [hc] using hnull) c.2.val)
    · simp
  unfold threeSpinProjection
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hn, Matrix.zero_mul]

 
theorem threeSpinProjection_sum (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ z ∈ Finset.range (Q+1), threeSpinProjection Q z) = 1 := by
  classical
  have hd : (∑ z ∈ Finset.range (Q+1), Matrix.diagonal
      (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=z then (1:ℂ) else 0)) = 1 := by
    ext c d
    simp only [Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases h : c=d
    · subst d
      simp only [ite_true]
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr (by have := coupledIndex_bounds c; omega))]
    · simp [h]
  simp only [threeSpinProjection, ← Matrix.sum_mul, ← Matrix.mul_sum]
  rw [hd, Matrix.mul_one, threeCouplingMatrix_complete Q (by omega)]

 

theorem normal_ordered_square_spectral (Q : ℕ) (hQ : 2 ≤ Q) :
    hamiltonian Q * hamiltonian Q = hamiltonian Q +
      exteriorLift Q 3 (threeWedgeMatrix Q *
        (∑ z ∈ Finset.range (Q+1), (gramShift Q z : ℂ) • threeSpinProjection Q z) *
          (threeWedgeMatrix Q)ᴴ) +
      exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) := by
  rw [← threeWedgeMatrix_gram_spectral Q hQ]
  exact normal_ordered_square Q (by omega)

end LaughlinFock
end

end OAI
