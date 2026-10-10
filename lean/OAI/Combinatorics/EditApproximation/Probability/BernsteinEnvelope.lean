import OAI.Combinatorics.EditApproximation.Geometry.PublishedInputs

namespace OAI

/-! The scalar exponential estimate used to discharge the finite Bernstein
input. Its rational majorant is proved by a derivative comparison, avoiding
any assumption of a concentration theorem. -/

namespace EditApproximation

noncomputable def bernsteinEnvelope (x : ℝ) : ℝ :=
  Real.exp (-x) * ((x ^ 2 + 4 * x + 6) / (6 - 2 * x))

private theorem bernsteinEnvelope_deriv (x : ℝ) (hx : x < 3) :
    HasDerivAt bernsteinEnvelope (Real.exp (-x) * (2 * x ^ 3 / (6 - 2 * x) ^ 2)) x := by
  have hd : (6 : ℝ) - 2 * x ≠ 0 := by linarith
  have hn := (((hasDerivAt_pow 2 x).add ((hasDerivAt_id x).const_mul 4)).add_const 6)
  have hb := (hasDerivAt_const x (6 : ℝ)).sub ((hasDerivAt_id x).const_mul 2)
  have h := ((hasDerivAt_id x).neg.exp).mul (hn.div hb hd)
  dsimp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq] at h
  unfold bernsteinEnvelope
  convert h using 1
  field_simp [hd]
  ring

private theorem bernsteinEnvelope_zero : bernsteinEnvelope 0 = 1 := by
  norm_num [bernsteinEnvelope]

theorem bernsteinEnvelope_one_le (x : ℝ) (hx : x < 3) : 1 ≤ bernsteinEnvelope x := by
  by_cases hpos : 0 ≤ x
  · have hc : ContinuousOn bernsteinEnvelope (Set.Icc 0 x) := by
      intro y hy
      exact (bernsteinEnvelope_deriv y (hy.2.trans_lt hx)).continuousAt.continuousWithinAt
    have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x) hc
      (fun y hy => (bernsteinEnvelope_deriv y ((interior_subset hy).2.trans_lt hx)).hasDerivWithinAt)
      (fun y hy => mul_nonneg (Real.exp_nonneg _) (div_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg (interior_subset hy).1 3)) (sq_nonneg _)))
    simpa only [bernsteinEnvelope_zero] using hm ⟨le_rfl, hpos⟩ ⟨hpos, le_rfl⟩ hpos
  · have hneg : x ≤ 0 := le_of_not_ge hpos
    have hc : ContinuousOn bernsteinEnvelope (Set.Icc x 0) := by
      intro y hy
      exact (bernsteinEnvelope_deriv y (by linarith [hy.2])).continuousAt.continuousWithinAt
    have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x 0) hc
      (fun y hy => (bernsteinEnvelope_deriv y (by linarith [(interior_subset hy).2])).hasDerivWithinAt)
      (fun y hy => mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (show y ^ 3 ≤ 0 by
          have h := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) (interior_subset hy).2
          nlinarith only [h]))
        (sq_nonneg _)))
    simpa only [bernsteinEnvelope_zero] using hm ⟨le_rfl, hneg⟩ ⟨hneg, le_rfl⟩ hneg

/-- Exact Bernstein exponential majorant, valid for all `x < 3`. -/
theorem exp_le_bernstein_envelope (x : ℝ) (hx : x < 3) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - x / 3)) := by
  have h := mul_le_mul_of_nonneg_left (bernsteinEnvelope_one_le x hx) (Real.exp_nonneg x)
  have hd : (6 : ℝ) - 2 * x ≠ 0 := by linarith
  have he : (2 : ℝ) * (1 - x / 3) ≠ 0 := by linarith
  have hc : (x ^ 2 + 4 * x + 6) / (6 - 2 * x) = 1 + x + x ^ 2 / (2 * (1 - x / 3)) := by
    have h3 : (3 : ℝ) - x ≠ 0 := by linarith
    field_simp [hd, he, h3]
    field_simp [show (6 : ℝ) - x * 2 ≠ 0 by linarith]
    ring
  simpa only [bernsteinEnvelope, mul_one, ← mul_assoc, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, one_mul, hc] using h

end EditApproximation

end OAI
