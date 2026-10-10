import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledBasisChange

namespace OAI

/-! # Fixed displacements shrink in positively weighted coordinates -/

namespace PolycyclicRecognition

open Module Filter
open scoped Topology

/-- Every fixed logarithmic displacement tends to zero when all coordinate
weights are positive. The scale parameter here is logarithmic. -/
theorem exponentialRescaleBasis_coordinates_tendsto_zero
    {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) (hcost : ∀ j, 0 < cost j) (x : L) :
    Tendsto (fun r : ℝ => (exponentialRescaleBasis b cost r).equivFun x)
      atTop (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro j
  have he (r : ℝ) : (exponentialRescaleBasis b cost r).equivFun x j =
      b.repr x j * Real.exp ((-cost j) * r) := by
    have hh := repr_exponentialRescaleBasis_smul b cost r 0 x j
    simp only [mul_zero, Real.exp_zero, one_smul, zero_sub] at hh
    change (exponentialRescaleBasis b cost r).repr x j = _
    rw [hh]
    congr 2
    ring
  have ht : Tendsto (fun r : ℝ => (-cost j) * r) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (neg_neg_of_pos (hcost j))).mpr tendsto_id
  have hlim := (Real.tendsto_exp_atBot.comp ht).const_mul (b.repr x j)
  simpa only [he, Pi.zero_apply, mul_zero, Function.comp_apply] using hlim

/-- Replacing a negative logarithmic scale by zero does not alter its
large-scale limit and gives a family defined with nonnegative scales. -/
theorem exponentialRescaleBasis_nonneg_coordinates_tendsto_zero
    {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) (hcost : ∀ j, 0 < cost j) (x : L) :
    Tendsto (fun r : ℝ => (exponentialRescaleBasis b cost (max r 0)).equivFun x)
      atTop (𝓝 0) := by
  apply (exponentialRescaleBasis_coordinates_tendsto_zero b cost hcost x).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  rw [max_eq_left hr]

end PolycyclicRecognition

end OAI
