import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolynomialBoxAbsorption

namespace OAI

/-! # Monotonicity of boxes with nonnegative exponential costs -/

noncomputable section
namespace PolycyclicRecognition

open Module

theorem norm_exponentialRescaleBasis_mono
    {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) (hcost : ∀ j, 0 ≤ cost j)
    {r t : ℝ} (hrt : r ≤ t) (v : L) :
    ‖(exponentialRescaleBasis b cost t).equivFun v‖ ≤
      ‖(exponentialRescaleBasis b cost r).equivFun v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  change |(exponentialRescaleBasis b cost t).repr v j| ≤ _
  rw [show t = r + (t - r) by ring, repr_shift_exponentialRescaleBasis,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hdecay : Real.exp (-(t - r) * cost j) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (hcost j))
  have hj := norm_le_pi_norm ((exponentialRescaleBasis b cost r).equivFun v) j
  exact (mul_le_mul_of_nonneg_right hdecay (abs_nonneg _)).trans (by simpa using hj)

theorem exponentialCoordinateBox_scale_mono
    {L J G : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (Exp : L → G) (b : Basis J ℝ L) (cost : J → ℝ) (hcost : ∀ j, 0 ≤ cost j)
    {r t R : ℝ} (hrt : r ≤ t) :
    exponentialCoordinateBox Exp (exponentialRescaleBasis b cost r) R ⊆
      exponentialCoordinateBox Exp (exponentialRescaleBasis b cost t) R := by
  rintro g ⟨v, hv, hn⟩
  exact ⟨v, hv, (norm_exponentialRescaleBasis_mono b cost hcost hrt v).trans hn⟩

end PolycyclicRecognition

end

end OAI
