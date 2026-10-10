import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWellMatrix

namespace OAI

/-! The unperturbed shifted multiwell matrix: its leading off-diagonal
entry is the actual hopping, and every remaining term has two tail factors.
No independent matrix approximation is assumed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def planarMultiwellMatrix {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  ∑ k, if k = j then 0 else planarWellMatrix (u i) (u j) (u k)

def planarHoppingMatrix {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) : ℝ :=
  if i = j then 0 else -planarHopping ‖u i - u j‖

theorem planarMultiwellMatrix_error_eq {m : ℕ} (u : Fin m → PlanarPosition) (i j : Fin m) :
    planarMultiwellMatrix u i j - planarHoppingMatrix u i j =
      ∑ k, if k ≠ i ∧ k ≠ j then planarWellMatrix (u i) (u j) (u k) else 0 := by
  classical
  have hpoint (k : Fin m) :
      (if k = j then 0 else planarWellMatrix (u i) (u j) (u k)) =
      (if k = i then (if i = j then 0 else planarWellMatrix (u i) (u j) (u i)) else 0) +
      (if k ≠ i ∧ k ≠ j then planarWellMatrix (u i) (u j) (u k) else 0) := by
    by_cases hki : k = i
    · subst k
      by_cases hij : i = j
      · subst j
        simp only [ite_true, ne_eq, not_true_eq_false, false_and, ite_false, add_zero]
      · simp only [hij, ite_false, ite_true, ne_eq, not_true_eq_false, false_and, add_zero]
    · by_cases hkj : k = j
      · subst k
        simp only [hki, ite_false, ite_true, ne_eq, not_true_eq_false, and_false, add_zero]
      · simp only [hki, hkj, ite_false, ne_eq, not_false_eq_true, and_self, ite_true, zero_add]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => hpoint k)
  unfold planarMultiwellMatrix planarHoppingMatrix
  rw [hsum, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, planarWellMatrix_hopping]
  ring

theorem planarMultiwellMatrix_error_bound {D : ℝ} {m : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (i j : Fin m) :
    |planarMultiwellMatrix u i j - planarHoppingMatrix u i j| ≤
      m * planarWellMatrixConstant * Real.exp (-(19 / 10 : ℝ) * D) := by
  rw [planarMultiwellMatrix_error_eq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _k : Fin m, planarWellMatrixConstant * Real.exp (-(19 / 10 : ℝ) * D) :=
      Finset.sum_le_sum (fun k _ => by
        split_ifs with hk
        · exact planarWellMatrix_two_far _ _ _ (hsep i k hk.1.symm) (hsep j k hk.2.symm)
        · rw [abs_zero]
          exact mul_nonneg planarWellMatrixConstant_nonnegative (Real.exp_pos _).le)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end ContinuumCoulomb

end

end OAI
