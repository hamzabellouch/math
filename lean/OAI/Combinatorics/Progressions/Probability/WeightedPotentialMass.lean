import Mathlib.Algebra.MvPolynomial.Eval
import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
import OAI.Combinatorics.Progressions.Polynomial.WeightedPolynomialPotential

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem weightedPolynomialPotential_map_real (w : σ → ℕ) (d : ℕ)
    (P : σ → MvPolynomial σ ℚ) :
    MvPolynomial.map (Rat.castHom ℝ) (weightedPolynomialPotential w d P) =
      ∑ i, C ((w i : ℝ) / d) * (X i * MvPolynomial.map (Rat.castHom ℝ) (P i)) := by
  classical
  rw [weightedPolynomialPotential, Finset.smul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, MvPolynomial.smul_eq_C_mul]
  simp [div_eq_mul_inv, mul_comm]

theorem realPolynomialMass_weightedPolynomialPotential_le
    (w : σ → ℕ) (d : ℕ) (P : σ → MvPolynomial σ ℚ) :
    realPolynomialMass
        (MvPolynomial.map (Rat.castHom ℝ) (weightedPolynomialPotential w d P)) ≤
      ∑ i, ((w i : ℝ) / d) *
        realPolynomialMass (MvPolynomial.map (Rat.castHom ℝ) (P i)) := by
  rw [weightedPolynomialPotential_map_real]
  apply (realPolynomialMass_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hw : 0 ≤ (w i : ℝ) / d := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ |(w i : ℝ) / d| *
        realPolynomialMass (X i * MvPolynomial.map (Rat.castHom ℝ) (P i)) :=
      realPolynomialMass_C_mul_le _ _
    _ ≤ ((w i : ℝ) / d) *
        (realPolynomialMass (X i) *
          realPolynomialMass (MvPolynomial.map (Rat.castHom ℝ) (P i))) := by
      rw [abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (realPolynomialMass_mul_le _ _) hw
    _ = _ := by rw [realPolynomialMass_X, one_mul]

theorem realPolynomialMass_weightedPolynomialPotential_uniform_le
    (w : σ → ℕ) {d : ℕ} (hd : 0 < d) (P : σ → MvPolynomial σ ℚ)
    (hweight : ∀ i, w i ≤ d) {C : ℝ}
    (hP : ∀ i, realPolynomialMass (MvPolynomial.map (Rat.castHom ℝ) (P i)) ≤ C) :
    realPolynomialMass
        (MvPolynomial.map (Rat.castHom ℝ) (weightedPolynomialPotential w d P)) ≤
      Fintype.card σ * C := by
  apply (realPolynomialMass_weightedPolynomialPotential_le w d P).trans
  calc
    _ ≤ ∑ _i : σ, C := by
      apply Finset.sum_le_sum
      intro i _
      have hw : (w i : ℝ) / d ≤ 1 :=
        (div_le_one (by exact_mod_cast hd)).mpr (by exact_mod_cast hweight i)
      exact (mul_le_of_le_one_left (realPolynomialMass_nonneg _) hw).trans (hP i)
    _ = _ := by simp

end Erdos3

end

end OAI
