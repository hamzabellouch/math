import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDerivativeBounds

namespace OAI

/-! # The quadratic remainder with constants uniform on expanding tori -/

open Set Metric

namespace DefocusingNLS

noncomputable def expandingNonlinearRemainder (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ)
    (q v : FourierL2) : FourierL2 :=
  expandingOddPower a k L ha ha1 hk hL m (q + v) -
    expandingOddPower a k L ha ha1 hk hL m q -
      fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) q v

@[simp] theorem expandingNonlinearRemainder_zero (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ)
    (q : FourierL2) : expandingNonlinearRemainder a k L ha ha1 hk hL m q 0 = 0 := by
  simp [expandingNonlinearRemainder]

theorem hasFDerivAt_expandingNonlinearRemainder (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ) (q v : FourierL2) :
    HasFDerivAt (expandingNonlinearRemainder a k L ha ha1 hk hL m q)
      (fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) (q + v) -
        fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) q) v := by
  have hN := ((contDiff_expandingOddPower a k L ha ha1 hk hL m).differentiable
    (by simp) (q + v)).hasFDerivAt
  have hshift : HasFDerivAt (fun z : FourierL2 => q + z)
      (ContinuousLinearMap.id ℝ FourierL2) v := (hasFDerivAt_id v).const_add q
  have h := ((hN.comp v hshift).sub_const (expandingOddPower a k L ha ha1 hk hL m q)).sub
    (fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) q).hasFDerivAt
  convert h using 1 <;> ext z <;> rfl

/-- One quadratic Lipschitz constant works on every torus with `L ≥ 1`. -/
theorem exists_expandingNonlinearRemainder_lipschitz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L) (q v w : FourierL2),
      ‖q‖ ≤ R → ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      ‖expandingNonlinearRemainder a k L ha ha1 hk hL m q v -
        expandingNonlinearRemainder a k L ha ha1 hk hL m q w‖ ≤
          C * (‖v‖ + ‖w‖) * ‖v - w‖ := by
  obtain ⟨C, hC, hCb⟩ := exists_expandingOddPower_derivative_lipschitz
    a k ha ha1 hk m (R + 1) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro L hL q v w hq hv hw
  let d := max ‖v‖ ‖w‖
  have hd : d ≤ 1 := max_le hv hw
  have hdb : ∀ z ∈ closedBall (0 : FourierL2) d,
      ‖fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) (q + z) -
        fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) q‖ ≤ C * d := by
    intro z hz
    have hzn : ‖z‖ ≤ d := by simpa using hz
    have hqz : ‖q + z‖ ≤ R + 1 := (norm_add_le q z).trans (by linarith)
    have h := hCb L hL (q + z) q hqz (by linarith)
    simp only [add_sub_cancel_left] at h
    exact h.trans (mul_le_mul_of_nonneg_left hzn hC)
  have hm := (convex_closedBall (0 : FourierL2) d).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hasFDerivAt_expandingNonlinearRemainder a k L ha ha1 hk hL m q z).hasFDerivWithinAt)
    hdb (show w ∈ closedBall (0 : FourierL2) d by simp [d])
    (show v ∈ closedBall (0 : FourierL2) d by simp [d])
  have hd' : d ≤ ‖v‖ + ‖w‖ := max_le
    (le_add_of_nonneg_right (norm_nonneg w)) (le_add_of_nonneg_left (norm_nonneg v))
  exact hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hd' hC) (norm_nonneg (v - w)))

/-- The quadratic remainder estimate has no dependence on the expanding scale. -/
theorem exists_expandingNonlinearRemainder_quadratic (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L) (q v : FourierL2),
      ‖q‖ ≤ R → ‖v‖ ≤ 1 →
      ‖expandingNonlinearRemainder a k L ha ha1 hk hL m q v‖ ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_expandingNonlinearRemainder_lipschitz a k ha ha1 hk m R hR
  refine ⟨C, hC, ?_⟩
  intro L hL q v hq hv
  simpa only [expandingNonlinearRemainder_zero, norm_zero, add_zero, sub_zero, pow_two, mul_assoc]
    using hb L hL q v 0 hq hv (by simp)

end DefocusingNLS

end OAI
