import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! Matrix operator action and norm perturbation estimates. -/

noncomputable section
open scoped BigOperators
namespace Kaplansky
variable {m n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev HilbertColumns (n : ℕ) (H : Type*) := PiLp 2 (fun _ : Fin n => H)

def operatorMatrixAction (W : Fin m → Fin n → H →L[ℂ] H) (v : HilbertColumns n H) :
    HilbertColumns m H := ∑ row, PiLp.single 2 row (∑ col, W row col (v col))

@[simp] theorem operatorMatrixAction_apply (W : Fin m → Fin n → H →L[ℂ] H)
    (v : HilbertColumns n H) (row : Fin m) :
    operatorMatrixAction W v row = ∑ col, W row col (v col) := by
  classical
  simp [operatorMatrixAction]

theorem operatorMatrixAction_norm_le (W : Fin m → Fin n → H →L[ℂ] H)
    {δ : ℝ} (hδ : 0≤δ) (hW : ∀ row col, ‖W row col‖ ≤ δ) (v : HilbertColumns n H) :
    ‖operatorMatrixAction W v‖ ≤ (m*n : ℝ)*δ*‖v‖ := by
  calc
    ‖operatorMatrixAction W v‖ ≤ ∑ row, ‖(PiLp.single 2 row (∑ col, W row col (v col)) : HilbertColumns m H)‖ := norm_sum_le _ _
    _ ≤ ∑ _row : Fin m, ∑ _col : Fin n, δ*‖v‖ := by
      apply Finset.sum_le_sum
      intro row _
      rw [PiLp.norm_single]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro col _
      exact (W row col).le_opNorm (v col) |>.trans
        (mul_le_mul (hW row col) (PiLp.norm_apply_le v col) (norm_nonneg _) hδ)
    _ = _ := by simp; ring

variable [CompleteSpace H]

/-- The rectangular matrix column identity implies a Hilbert-space
isometry, with no finite-dimensional assumption on the Hilbert fibers. -/
theorem operatorMatrixAction_inner (W : Fin m → Fin n → H →L[ℂ] H)
    (hW : ∀ i j, (∑ row, (W row i).adjoint.comp (W row j)) =
      if i=j then ContinuousLinearMap.id ℂ H else 0)
    (v w : HilbertColumns n H) :
    inner ℂ (operatorMatrixAction W v) (operatorMatrixAction W w)=inner ℂ v w := by
  classical
  simp only [PiLp.inner_apply,operatorMatrixAction_apply,sum_inner,inner_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  have he (j : Fin n) : (∑ row, inner ℂ (W row j (v j)) (W row i (w i))) =
      inner ℂ (v j) ((∑ row, (W row j).adjoint.comp (W row i)) (w i)) := by
    simp only [sum_apply,ContinuousLinearMap.comp_apply,inner_sum,
      ContinuousLinearMap.adjoint_inner_right]
  simp only [he,hW]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem operatorMatrixAction_norm (W : Fin m → Fin n → H →L[ℂ] H)
    (hW : ∀ i j, (∑ row, (W row i).adjoint.comp (W row j)) =
      if i=j then ContinuousLinearMap.id ℂ H else 0) (v : HilbertColumns n H) :
    ‖operatorMatrixAction W v‖=‖v‖ := by
  have he := congrArg RCLike.re (operatorMatrixAction_inner W hW v v)
  simp only [inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (operatorMatrixAction W v),norm_nonneg v]

end Kaplansky

end

noncomputable section
open scoped BigOperators
namespace Kaplansky
variable {m n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem operatorMatrixAction_sub (P W : Fin m → Fin n → H →L[ℂ] H)
    (v : HilbertColumns n H) :
    operatorMatrixAction (P-W) v = operatorMatrixAction P v - operatorMatrixAction W v := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => H)).injective
  funext row
  change operatorMatrixAction (P-W) v row = operatorMatrixAction P v row-operatorMatrixAction W v row
  simp only [operatorMatrixAction_apply,Pi.sub_apply,sub_apply,
    Finset.sum_sub_distrib]

theorem operatorMatrix_perturbation_lower_bound (P W : Fin m → Fin n → H →L[ℂ] H)
    (hW : ∀ v : HilbertColumns n H, ‖operatorMatrixAction W v‖=‖v‖)
    {δ : ℝ} (hδ : 0≤δ) (hclose : ∀ i j, ‖P i j-W i j‖ ≤ δ)
    (v : HilbertColumns n H) :
    (1-(m*n : ℝ)*δ)*‖v‖ ≤ ‖operatorMatrixAction P v‖ := by
  have hd := operatorMatrixAction_norm_le (P-W) hδ hclose v
  rw [operatorMatrixAction_sub] at hd
  have he : operatorMatrixAction W v =
      (operatorMatrixAction W v-operatorMatrixAction P v)+operatorMatrixAction P v := by simp
  have hb : ‖v‖ ≤ ‖operatorMatrixAction P v-operatorMatrixAction W v‖+‖operatorMatrixAction P v‖ := by
    rw [← hW v]
    conv_lhs => rw [he]
    simpa only [norm_sub_rev] using norm_add_le
      (operatorMatrixAction W v-operatorMatrixAction P v) (operatorMatrixAction P v)
  nlinarith

end Kaplansky

end

end OAI
