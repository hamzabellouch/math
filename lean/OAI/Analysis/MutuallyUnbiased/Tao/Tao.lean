import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import OAI.Analysis.MutuallyUnbiased.Model

namespace OAI

/-! The explicit five-cycle representative of Tao's cubic matrix. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem omega_isPrimitiveRoot : IsPrimitiveRoot omega 3 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 3 (by decide)

theorem omega_cube : omega ^ 3 = 1 := omega_isPrimitiveRoot.pow_eq_one

theorem omega_norm : ‖omega‖ = 1 :=
  omega_isPrimitiveRoot.norm'_eq_one (by decide)

theorem omega_normSq : Complex.normSq omega = 1 := by
  rw [Complex.normSq_eq_norm_sq, omega_norm]
  norm_num

theorem omega_sum : 1 + omega + omega ^ 2 = 0 := by
  simpa [Finset.sum_range_succ] using
    omega_isPrimitiveRoot.geom_sum_eq_zero (by decide : 1 < 3)

theorem omega_conj : conj omega = omega ^ 2 := by
  have homega : omega ≠ 0 := by
    intro hzero
    simpa [hzero] using omega_normSq
  apply mul_left_cancel₀ homega
  calc
    omega * conj omega = 1 := by simp [Complex.mul_conj, omega_normSq]
    _ = omega * omega ^ 2 := by rw [← pow_succ', omega_cube]

theorem omega_four : omega ^ 4 = omega := by
  calc
    omega ^ 4 = omega ^ 3 * omega := by ring
    _ = omega := by rw [omega_cube]; simp

theorem omega_five : omega ^ 5 = omega ^ 2 := by
  calc
    omega ^ 5 = omega ^ 3 * omega ^ 2 := by ring
    _ = omega ^ 2 := by rw [omega_cube]; simp

theorem omega_six : omega ^ 6 = 1 := by
  calc
    omega ^ 6 = (omega ^ 3) ^ 2 := by ring
    _ = 1 := by rw [omega_cube]; norm_num

theorem tao_entries_unit (i j : Coord) : Complex.normSq (tao i j) = 1 := by
  simp [tao, map_pow, omega_normSq]

theorem tao_gram : tao.conjTranspose * tao = (6 : ℂ) • (1 : CMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tao, taoExponent, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, omega_conj] <;>
    ring_nf <;>
    norm_num [omega_cube, omega_four, omega_five, omega_six] <;>
    linear_combination 2 * omega_sum

theorem tao_isHadamard : IsHadamard tao := ⟨tao_entries_unit, tao_gram⟩

theorem isHadamard_conj {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard (fun i j => conj (H i j)) := by
  refine ⟨?_, ?_⟩
  · intro i j
    simpa using hH.1 i j
  · ext i j
    have h := congrArg (fun A : CMatrix => conj (A i j)) hH.2
    change (∑ k, conj (conj (H k i)) * conj (H k j)) =
      (6 : ℂ) * (if i = j then 1 else 0)
    by_cases hij : i = j <;>
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply, map_sum, map_ofNat, hij] using h

theorem tao_square_eq_conj :
    (fun i j => (tao i j) ^ 2) = (fun i j => conj (tao i j)) := by
  funext i j
  simp [tao, omega_conj, ← pow_mul, Nat.mul_comm]

theorem tao_square_isHadamard : IsHadamard (fun i j => (tao i j) ^ 2) := by
  rw [tao_square_eq_conj]
  exact isHadamard_conj tao_isHadamard

end MUB6

end

end OAI
