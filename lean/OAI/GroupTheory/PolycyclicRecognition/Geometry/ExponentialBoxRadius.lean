import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledMetricSmallness

namespace OAI

/-! # Absorbing a subexponential radius into a larger box scale -/

noncomputable section

namespace PolycyclicRecognition

open Module

/-- Doubling the scale absorbs a radius `exp (r ε)` whenever every
coordinate cost is at least `ε`. -/
theorem norm_double_scale_le_one
    {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) {r ε : ℝ} (hr : 0 ≤ r)
    (hcost : ∀ j, ε ≤ cost j) (v : L)
    (hv : ‖(exponentialRescaleBasis b cost r).equivFun v‖ ≤ Real.exp (r * ε)) :
    ‖(exponentialRescaleBasis b cost (2 * r)).equivFun v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  change |(exponentialRescaleBasis b cost (2 * r)).repr v j| ≤ 1
  rw [two_mul, repr_shift_exponentialRescaleBasis, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-r * cost j) * Real.exp (r * ε) :=
      mul_le_mul_of_nonneg_left
        ((norm_le_pi_norm ((exponentialRescaleBasis b cost r).equivFun v) j).trans hv)
        (Real.exp_pos _).le
    _ = Real.exp (r * (ε - cost j)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr (hcost j)))

end PolycyclicRecognition

end

end OAI
