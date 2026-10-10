import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDerivativeBounds
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearization

namespace OAI

/-! # The quadratic homogeneous remainder after linearization -/

open Set Metric
open scoped ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

/-- The actual odd-power nonlinearity with its constant and linear parts removed. -/
noncomputable def homogeneousNonlinearRemainder (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q v : (HomogeneousY a k)) : (HomogeneousY a k) :=
  homogeneousOddPower a k ha ha1 hk m (q + v) - homogeneousOddPower a k ha ha1 hk m q -
    fderiv ℝ (homogeneousOddPower a k ha ha1 hk m) q v

@[simp] theorem homogeneousNonlinearRemainder_zero (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q : (HomogeneousY a k)) : homogeneousNonlinearRemainder a k ha ha1 hk m q 0 = 0 := by
  simp [homogeneousNonlinearRemainder]

/-- The completed-space remainder is exactly the pointwise physical remainder. -/
theorem homogeneousNonlinearRemainder_physical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q v : HomogeneousY a k) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousNonlinearRemainder a k ha ha1 hk m q v) y =
      oddPowerNonlinearity m
          (homogeneousPhysicalCLM a k ha ha1 hk q y + homogeneousPhysicalCLM a k ha ha1 hk v y) -
        oddPowerNonlinearity m (homogeneousPhysicalCLM a k ha ha1 hk q y) -
          oddPowerDerivative m (homogeneousPhysicalCLM a k ha ha1 hk q y)
            (homogeneousPhysicalCLM a k ha ha1 hk v y) := by
  simp only [homogeneousNonlinearRemainder, map_sub, ZeroAtInftyContinuousMap.sub_apply,
    homogeneousOddPower_physical, homogeneousOddPower_fderiv_physical, map_add,
    ZeroAtInftyContinuousMap.add_apply]

theorem hasFDerivAt_homogeneousNonlinearRemainder (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q v : (HomogeneousY a k)) :
    HasFDerivAt (homogeneousNonlinearRemainder a k ha ha1 hk m q)
      (fderiv ℝ (homogeneousOddPower a k ha ha1 hk m) (q + v) -
        fderiv ℝ (homogeneousOddPower a k ha ha1 hk m) q) v := by
  have hN := ((contDiff_homogeneousOddPower a k ha ha1 hk m).differentiable (by simp) (q + v)).hasFDerivAt
  have hshift : HasFDerivAt (fun z : (HomogeneousY a k) => q + z)
      (ContinuousLinearMap.id ℝ (HomogeneousY a k)) v := (hasFDerivAt_id v).const_add q
  have h := ((hN.comp v hshift).sub_const (homogeneousOddPower a k ha ha1 hk m q)).sub
    (fderiv ℝ (homogeneousOddPower a k ha ha1 hk m) q).hasFDerivAt
  convert h using 1 <;> ext z <;> rfl

/-- On any bounded set of backgrounds, the linearized remainder has the manuscript's
quadratic Lipschitz bound, uniformly for perturbations in the unit ball. -/
theorem exists_homogeneousNonlinearRemainder_lipschitz (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q v w : (HomogeneousY a k), ‖q‖ ≤ R → ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      ‖homogeneousNonlinearRemainder a k ha ha1 hk m q v - homogeneousNonlinearRemainder a k ha ha1 hk m q w‖ ≤
        C * (‖v‖ + ‖w‖) * ‖v - w‖ := by
  obtain ⟨C, hC, hCb⟩ := exists_homogeneousOddPower_derivative_lipschitz a k ha ha1 hk m (R + 1) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro q v w hq hv hw
  let d := max ‖v‖ ‖w‖
  have hd : d ≤ 1 := max_le hv hw
  have hdb : ∀ z ∈ closedBall (0 : (HomogeneousY a k)) d,
      ‖fderiv ℝ (homogeneousOddPower a k ha ha1 hk m) (q + z) -
        fderiv ℝ (homogeneousOddPower a k ha ha1 hk m) q‖ ≤ C * d := by
    intro z hz
    have hzn : ‖z‖ ≤ d := by simpa using hz
    have hqz : ‖q + z‖ ≤ R + 1 := (norm_add_le q z).trans (by linarith)
    have h := hCb (q + z) q hqz (by linarith)
    simp only [add_sub_cancel_left] at h
    exact h.trans (mul_le_mul_of_nonneg_left hzn hC)
  have hm := (convex_closedBall (0 : (HomogeneousY a k)) d).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hasFDerivAt_homogeneousNonlinearRemainder a k ha ha1 hk m q z).hasFDerivWithinAt) hdb
    (show w ∈ closedBall (0 : (HomogeneousY a k)) d by simp [d])
    (show v ∈ closedBall (0 : (HomogeneousY a k)) d by simp [d])
  have hd' : d ≤ ‖v‖ + ‖w‖ := max_le
    (le_add_of_nonneg_right (norm_nonneg w)) (le_add_of_nonneg_left (norm_nonneg v))
  exact hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hd' hC) (norm_nonneg (v - w)))

/-- The remainder is quadratic, with one constant for every background in a fixed homogeneous-space ball. -/
theorem exists_homogeneousNonlinearRemainder_quadratic (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q v : (HomogeneousY a k), ‖q‖ ≤ R → ‖v‖ ≤ 1 →
      ‖homogeneousNonlinearRemainder a k ha ha1 hk m q v‖ ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_homogeneousNonlinearRemainder_lipschitz a k ha ha1 hk m R hR
  refine ⟨C, hC, ?_⟩
  intro q v hq hv
  simpa only [homogeneousNonlinearRemainder_zero, norm_zero, add_zero, sub_zero, pow_two, mul_assoc]
    using hb q v 0 hq hv (by simp)

end DefocusingNLS

end OAI
