import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevSecondDerivativeBounds

namespace OAI

/-! # The quadratic Sobolev remainder after linearization -/

open Set Metric

namespace DefocusingNLS

/-- The actual odd-power nonlinearity with its constant and linear parts removed. -/
noncomputable def sobolevNonlinearRemainder (k : ℝ) (hk : 6 < k) (m : ℕ)
    (q v : FourierL2) : FourierL2 :=
  sobolevOddPower k hk m (q + v) - sobolevOddPower k hk m q -
    fderiv ℝ (sobolevOddPower k hk m) q v

@[simp] theorem sobolevNonlinearRemainder_zero (k : ℝ) (hk : 6 < k) (m : ℕ)
    (q : FourierL2) : sobolevNonlinearRemainder k hk m q 0 = 0 := by
  simp [sobolevNonlinearRemainder]

theorem hasFDerivAt_sobolevNonlinearRemainder (k : ℝ) (hk : 6 < k) (m : ℕ)
    (q v : FourierL2) :
    HasFDerivAt (sobolevNonlinearRemainder k hk m q)
      (fderiv ℝ (sobolevOddPower k hk m) (q + v) -
        fderiv ℝ (sobolevOddPower k hk m) q) v := by
  have hN := ((contDiff_sobolevOddPower k hk m).differentiable (by simp) (q + v)).hasFDerivAt
  have hshift : HasFDerivAt (fun z : FourierL2 => q + z)
      (ContinuousLinearMap.id ℝ FourierL2) v := (hasFDerivAt_id v).const_add q
  have h := ((hN.comp v hshift).sub_const (sobolevOddPower k hk m q)).sub
    (fderiv ℝ (sobolevOddPower k hk m) q).hasFDerivAt
  convert h using 1 <;> ext z <;> rfl

/-- On any bounded set of backgrounds, the linearized remainder has the manuscript's
quadratic Lipschitz bound, uniformly for perturbations in the unit ball. -/
theorem exists_sobolevNonlinearRemainder_lipschitz (k : ℝ) (hk : 6 < k) (m : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q v w : FourierL2, ‖q‖ ≤ R → ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      ‖sobolevNonlinearRemainder k hk m q v - sobolevNonlinearRemainder k hk m q w‖ ≤
        C * (‖v‖ + ‖w‖) * ‖v - w‖ := by
  obtain ⟨C, hC, hCb⟩ := exists_sobolevOddPower_derivative_lipschitz k hk m (R + 1) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro q v w hq hv hw
  let d := max ‖v‖ ‖w‖
  have hd : d ≤ 1 := max_le hv hw
  have hdb : ∀ z ∈ closedBall (0 : FourierL2) d,
      ‖fderiv ℝ (sobolevOddPower k hk m) (q + z) -
        fderiv ℝ (sobolevOddPower k hk m) q‖ ≤ C * d := by
    intro z hz
    have hzn : ‖z‖ ≤ d := by simpa using hz
    have hqz : ‖q + z‖ ≤ R + 1 := (norm_add_le q z).trans (by linarith)
    have h := hCb (q + z) q hqz (by linarith)
    simp only [add_sub_cancel_left] at h
    exact h.trans (mul_le_mul_of_nonneg_left hzn hC)
  have hm := (convex_closedBall (0 : FourierL2) d).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hasFDerivAt_sobolevNonlinearRemainder k hk m q z).hasFDerivWithinAt) hdb
    (show w ∈ closedBall (0 : FourierL2) d by simp [d])
    (show v ∈ closedBall (0 : FourierL2) d by simp [d])
  have hd' : d ≤ ‖v‖ + ‖w‖ := max_le
    (le_add_of_nonneg_right (norm_nonneg w)) (le_add_of_nonneg_left (norm_nonneg v))
  exact hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hd' hC) (norm_nonneg (v - w)))

/-- The remainder is quadratic, with one constant for every background in a fixed Sobolev ball. -/
theorem exists_sobolevNonlinearRemainder_quadratic (k : ℝ) (hk : 6 < k) (m : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q v : FourierL2, ‖q‖ ≤ R → ‖v‖ ≤ 1 →
      ‖sobolevNonlinearRemainder k hk m q v‖ ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_sobolevNonlinearRemainder_lipschitz k hk m R hR
  refine ⟨C, hC, ?_⟩
  intro q v hq hv
  simpa only [sobolevNonlinearRemainder_zero, norm_zero, add_zero, sub_zero, pow_two, mul_assoc]
    using hb q v 0 hq hv (by simp)

end DefocusingNLS

end OAI
