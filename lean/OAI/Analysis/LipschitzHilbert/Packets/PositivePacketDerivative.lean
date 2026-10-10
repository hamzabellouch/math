import OAI.Analysis.LipschitzHilbert.Packets.PositivePacketSquare
import OAI.Analysis.LipschitzHilbert.Estimates.EnvelopeDerivative

namespace OAI

/-! Actual derivative bounds for the positive packet square function. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert.LinePacketFamily

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

theorem envelope_continuous (P : LinePacketFamily N κ ι) (j : Fin N) (i : ι j) :
    Continuous (P.envelope j i) := by
  exact continuous_iff_continuousAt.mpr (fun x =>
    (lineEnvelope_three_hasDerivAt (P.centerX j i) (P.length j) x).continuousAt.mul continuousAt_const)

theorem positiveScale_continuous (P : LinePacketFamily N κ ι) (j : Fin N) :
    Continuous (P.positiveScale j) :=
  continuous_finsetSum _ (fun i _ => (P.envelope_continuous j i).const_mul _)

theorem positiveScale_hasDerivAt (P : LinePacketFamily N κ ι) (j : Fin N) (x : ℝ) :
    HasDerivAt (P.positiveScale j)
      (∑ i, ‖P.coeff j i‖ * (deriv (lineEnvelope (P.centerX j i) (P.length j) 3) x *
        lineEnvelope (P.centerZ j i) P.width 2 P.lineY)) x := by
  have hd (i : ι j) := ((lineEnvelope_three_hasDerivAt (P.centerX j i) (P.length j) x).mul_const
    (lineEnvelope (P.centerZ j i) P.width 2 P.lineY)).const_mul ‖P.coeff j i‖
  have heq : P.positiveScale j = ∑ i, (fun x => ‖P.coeff j i‖ * P.envelope j i x) := by
    funext x
    simp only [positiveScale, Finset.sum_apply]
  rw [heq]
  apply HasDerivAt.sum
  intro i _
  simpa only [envelope, (lineEnvelope_three_hasDerivAt (P.centerX j i) (P.length j) x).deriv] using hd i

theorem positiveScale_derivative_bound (P : LinePacketFamily N κ ι) (j : Fin N) (x : ℝ) :
    |deriv (P.positiveScale j) x| ≤ (6 / P.length j) * P.positiveScale j x := by
  rw [(P.positiveScale_hasDerivAt j x).deriv]
  calc
    _ ≤ ∑ i, |‖P.coeff j i‖ * (deriv (lineEnvelope (P.centerX j i) (P.length j) 3) x *
        lineEnvelope (P.centerZ j i) P.width 2 P.lineY)| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (s := Finset.univ)
        (f := fun i => ‖P.coeff j i‖ * (deriv (lineEnvelope (P.centerX j i) (P.length j) 3) x *
          lineEnvelope (P.centerZ j i) P.width 2 P.lineY))
    _ ≤ ∑ i, ‖P.coeff j i‖ * (((6 / P.length j) * lineEnvelope (P.centerX j i) (P.length j) 3 x) *
        lineEnvelope (P.centerZ j i) P.width 2 P.lineY) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg _),
        abs_of_nonneg (lineEnvelope_nonneg _ _ _ _)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (lineEnvelope_three_derivative_bound _ _ _ (P.length_pos j))
          (lineEnvelope_nonneg _ _ _ _)) (norm_nonneg _)
    _ = _ := by
      simp only [positiveScale, envelope, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem positiveScale_square_hasDerivAt (P : LinePacketFamily N κ ι) (j : Fin N) (x : ℝ) :
    HasDerivAt (fun x => P.positiveScale j x ^ 2)
      (2 * P.positiveScale j x * deriv (P.positiveScale j) x) x := by
  convert (P.positiveScale_hasDerivAt j x).differentiableAt.hasDerivAt.pow 2 using 1
  norm_num

theorem positiveScale_square_derivative_bound (P : LinePacketFamily N κ ι) (j : Fin N) (x : ℝ) :
    |deriv (fun x => P.positiveScale j x ^ 2) x| ≤ (12 * (4 * Real.pi) ^ 4) / P.length j := by
  rw [(P.positiveScale_square_hasDerivAt j x).deriv, abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (P.positiveScale_bound j x).1]
  have hlen := P.length_pos j
  have h := mul_le_mul (P.positiveScale_bound j x).2 (P.positiveScale_derivative_bound j x)
    (abs_nonneg _) (by positivity : 0 ≤ (4 * Real.pi)^2)
  have h' := mul_le_mul_of_nonneg_left (P.positiveScale_bound j x).2
    (by positivity : 0 ≤ 6 / P.length j)
  calc
    _ ≤ 2 * ((4 * Real.pi)^2 * ((6 / P.length j) * P.positiveScale j x)) := by nlinarith
    _ ≤ 2 * ((4 * Real.pi)^2 * ((6 / P.length j) * (4 * Real.pi)^2)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h' (by positivity)) (by norm_num)
    _ = _ := by ring

end LipschitzHilbert.LinePacketFamily

end

end OAI
