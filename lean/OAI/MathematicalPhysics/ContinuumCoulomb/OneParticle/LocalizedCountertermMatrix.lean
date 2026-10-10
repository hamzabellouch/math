import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCounterterms
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWellOverlap

namespace OAI

/-! Actual counterterm matrix estimates: the onsite term is the required
negative direct-interaction sum; other diagonal terms have two tails and
off-diagonal terms have the actual overlap decay. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def localizedCountertermMatrix (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  ∑ k, localizedCounterterm freq u k * planarWellMatrix (u i) (u j) (u k)

theorem localizedCountertermMatrix_diagonal_error_eq (freq : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) :
    localizedCountertermMatrix freq u i i + localizedOffsiteSum freq u i =
      ∑ k, if k = i then 0 else localizedCounterterm freq u k * planarWellMatrix (u i) (u i) (u k) := by
  classical
  have hpoint (k : Fin m) :
      localizedCounterterm freq u k * planarWellMatrix (u i) (u i) (u k) =
      (if k = i then localizedCounterterm freq u i * planarWellMatrix (u i) (u i) (u i) else 0) +
      (if k = i then 0 else localizedCounterterm freq u k * planarWellMatrix (u i) (u i) (u k)) := by
    by_cases hk : k = i
    · subst k
      simp only [ite_true, add_zero]
    · simp only [hk, ite_false, zero_add]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => hpoint k)
  unfold localizedCountertermMatrix
  rw [hs, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, localizedCounterterm_diagonal]
  ring

theorem localizedCountertermMatrix_diagonal_error_bound {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖) (i : Fin m) :
    |localizedCountertermMatrix freq u i i + localizedOffsiteSum freq u i| ≤
      (m : ℝ) ^ 2 * localizedCountertermBound freq * planarWellMatrixConstant *
        Real.exp (-(19 / 10 : ℝ) * D) := by
  rw [localizedCountertermMatrix_diagonal_error_eq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _k : Fin m, (m * localizedCountertermBound freq) *
        (planarWellMatrixConstant * Real.exp (-(19 / 10 : ℝ) * D)) := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs with hk
      · rw [abs_zero]
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (localizedCountertermBound_nonnegative freq))
          (mul_nonneg planarWellMatrixConstant_nonnegative (Real.exp_pos _).le)
      · rw [abs_mul, abs_of_nonneg (localizedCounterterm_nonnegative freq u k)]
        exact mul_le_mul (localizedCounterterm_bound hfreq u k)
          (planarWellMatrix_two_far _ _ _ (hsep i k (Ne.symm hk)) (hsep i k (Ne.symm hk)))
          (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg m) (localizedCountertermBound_nonnegative freq))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem localizedCountertermMatrix_offdiagonal_bound {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    |localizedCountertermMatrix freq u i j| ≤
      (m : ℝ) ^ 2 * localizedCountertermBound freq *
        (PlanarSobolev.wellBound * planarOverlapConstant) * Real.exp (-(9 / 10 : ℝ) * ‖u i - u j‖) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _k : Fin m, (m * localizedCountertermBound freq) *
        ((PlanarSobolev.wellBound * planarOverlapConstant) * Real.exp (-(9 / 10 : ℝ) * ‖u i - u j‖)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_of_nonneg (localizedCounterterm_nonnegative freq u k)]
      exact mul_le_mul (localizedCounterterm_bound hfreq u k) (planarWellMatrix_overlap_decay _ _ _)
        (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg m) (localizedCountertermBound_nonnegative freq))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end ContinuumCoulomb

end

end OAI
