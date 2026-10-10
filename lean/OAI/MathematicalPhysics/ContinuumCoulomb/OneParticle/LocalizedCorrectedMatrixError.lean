import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCorrectedOneBody

namespace OAI

/-! Quantitative comparison of the actual shifted and scaled one-body
matrix with the hopping and Coulomb occupancy counterterm matrix. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def localizedOneBodyTarget (scale freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (i j : Fin m) : ℝ :=
  scale * planarHoppingMatrix u i j - if i=j then localizedOffsiteSum freq u i else 0

theorem localizedCorrectedOneBodyMatrix_error {freq scale D : ℝ} (hfreq : 0 < freq)
    (hscale : scale ≠ 0) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (i j : Fin m) :
    |scale * localizedCorrectedOneBodyMatrix freq scale u i j - localizedOneBodyTarget scale freq u i j| ≤
      (|scale| * m * planarWellMatrixConstant +
        (m : ℝ)^2 * localizedCountertermBound freq * planarWellMatrixConstant) *
          Real.exp (-(19/10 : ℝ)*D) +
        (m : ℝ)^2 * localizedCountertermBound freq *
          (PlanarSobolev.wellBound * planarOverlapConstant) * Real.exp (-(9/10 : ℝ)*D) := by
  classical
  let e₁ := |scale| * m * planarWellMatrixConstant * Real.exp (-(19/10 : ℝ)*D)
  let e₂ := (m : ℝ)^2 * localizedCountertermBound freq * planarWellMatrixConstant *
    Real.exp (-(19/10 : ℝ)*D)
  let e₃ := (m : ℝ)^2 * localizedCountertermBound freq *
    (PlanarSobolev.wellBound * planarOverlapConstant) * Real.exp (-(9/10 : ℝ)*D)
  have he₂ : 0 ≤ e₂ := by
    dsimp [e₂]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (localizedCountertermBound_nonnegative freq))
      planarWellMatrixConstant_nonnegative) (Real.exp_pos _).le
  have he₃ : 0 ≤ e₃ := by
    dsimp [e₃]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (localizedCountertermBound_nonnegative freq))
      (mul_nonneg PlanarSobolev.wellBound_nonnegative planarOverlapConstant_nonnegative)) (Real.exp_pos _).le
  have hb : |scale * (localizedOneBodyMatrix freq u i j - planarHoppingMatrix u i j)| ≤ e₁ := by
    rw [abs_mul, localizedOneBodyMatrix_eq hfreq]
    exact (mul_le_mul_of_nonneg_left (planarMultiwellMatrix_error_bound u hsep i j) (abs_nonneg scale)).trans_eq
      (by dsimp [e₁]; ring)
  have hc : |localizedCountertermMatrix freq u i j +
      (if i=j then localizedOffsiteSum freq u i else 0)| ≤ e₂+e₃ := by
    by_cases hij : i=j
    · subst j
      simp only [ite_true]
      exact (localizedCountertermMatrix_diagonal_error_bound hfreq u hsep i).trans (le_add_of_nonneg_right he₃)
    · simp only [hij, ite_false, add_zero]
      have h := localizedCountertermMatrix_offdiagonal_bound hfreq u i j
      have h' : |localizedCountertermMatrix freq u i j| ≤ e₃ := h.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith [hsep i j hij])) (by
          exact mul_nonneg (mul_nonneg (sq_nonneg _) (localizedCountertermBound_nonnegative freq))
            (mul_nonneg PlanarSobolev.wellBound_nonnegative planarOverlapConstant_nonnegative)))
      exact h'.trans (le_add_of_nonneg_left he₂)
  rw [localizedCorrectedOneBodyMatrix_scaled hfreq hscale]
  unfold localizedOneBodyTarget
  have hid : scale * localizedOneBodyMatrix freq u i j + localizedCountertermMatrix freq u i j -
      (scale * planarHoppingMatrix u i j - if i=j then localizedOffsiteSum freq u i else 0) =
      scale * (localizedOneBodyMatrix freq u i j - planarHoppingMatrix u i j) +
        (localizedCountertermMatrix freq u i j + if i=j then localizedOffsiteSum freq u i else 0) := by ring
  rw [hid]
  calc
    _ ≤ |scale*(localizedOneBodyMatrix freq u i j-planarHoppingMatrix u i j)| +
        |localizedCountertermMatrix freq u i j + if i=j then localizedOffsiteSum freq u i else 0| := abs_add_le _ _
    _ ≤ e₁+(e₂+e₃) := add_le_add hb hc
    _ = _ := by dsimp [e₁,e₂,e₃]; ring

end ContinuumCoulomb

end

end OAI
