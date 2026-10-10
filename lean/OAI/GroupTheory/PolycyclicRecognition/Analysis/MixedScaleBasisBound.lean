import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledBasisChange

namespace OAI

/-! # Coordinate comparison from the actual exponential widths -/

namespace PolycyclicRecognition
open Module

/-- Only the products of physical scale and word cost matter for a box. -/
theorem norm_exponentialRescaleBasis_le_of_exponents_le
    {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (b : Basis J ℝ L) (u v : J → ℝ) (r t : ℝ)
    (h : ∀ j, t * v j ≤ r * u j) (x : L) :
    ‖(exponentialRescaleBasis b u r).equivFun x‖ ≤
      ‖(exponentialRescaleBasis b v t).equivFun x‖ := by
  have hh := norm_change_exponentialRescaleBasis_le b (fun j => r * u j)
    (fun j => t * v j) zero_le_one (α := 0)
    (fun j => sub_nonpos.mpr (h j)) x
  simpa only [exponentialRescaleBasis, one_mul, mul_zero, Real.exp_zero] using hh

end PolycyclicRecognition

end OAI
