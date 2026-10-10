import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.EulerRegisters
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.RoundedEuler

namespace OAI

/-! Componentwise box projection preserves Euclidean distance to every
point in the box. Rounding the projected numerator adds at most `3 / D`;
there is no multiplicative loss in the Euler error recurrence. -/

noncomputable section
namespace ContinuumCoulomb.EulerRegisters
open CappedKernelProgram (Triple position)

private theorem norm_le_of_abs_le (x y : Position)
    (h : ∀ a, |x a| ≤ |y a|) : ‖x‖ ≤ ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro a _
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (h a)

theorem norm_of_coordinate_error {x y : Position} {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ a, |x a| ≤ |y a|+d) : ‖x‖ ≤ ‖y‖+3*d := by
  let a : Position := WithLp.toLp 2 (fun i => |y i|)
  let b : Position := WithLp.toLp 2 (fun _ : Fin 3 => d)
  have ha : ‖a‖ = ‖y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    simp only [a,sq_abs]
  have hb : ‖b‖ ≤ 3*d := by
    have hs : ‖b‖^2 = 3*d^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [b,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_ofNat]
    nlinarith [norm_nonneg b]
  have hc : ‖x‖ ≤ ‖a+b‖ := by
    apply norm_le_of_abs_le
    intro i
    simpa only [a,b,PiLp.add_apply,PiLp.toLp_apply,abs_of_nonneg (add_nonneg (abs_nonneg _) hd)] using h i
  exact hc.trans ((norm_add_le a b).trans (by rw [ha]; linarith))

theorem round_position_error {D B : ℕ} (hD : 0 < D) (q : Triple) (x : Position)
    (hx : ∀ a, |x a| ≤ (B:ℝ)/(D:ℝ)) :
    ‖position (point D (round D B q))-x‖ ≤ ‖position q-x‖+3/(D:ℝ) := by
  have hd : (0:ℝ) ≤ 1/(D:ℝ) := by positivity
  have hc (a : Fin 3) :
      |(position (point D (round D B q))-x) a| ≤ |(position q-x) a|+1/(D:ℝ) := by
    fin_cases a <;>
      simpa [point,round,position,RationalBoxRound.value] using RationalBoxRound.value_error hD _ _ (hx _)
  have he := norm_of_coordinate_error hd hc
  simpa only [mul_one_div] using he

theorem proposal_position (h : ℚ) (q v : Triple) :
    position (proposal h q v) = position q+(h:ℝ) • position v := by
  ext a
  fin_cases a <;> simp [proposal,position]

end ContinuumCoulomb.EulerRegisters

end

end OAI
