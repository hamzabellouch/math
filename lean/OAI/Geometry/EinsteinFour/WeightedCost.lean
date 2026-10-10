import OAI.Geometry.EinsteinFour.ProjectionCost
import OAI.Geometry.EinsteinFour.HessianTraceEquation

namespace OAI

/-! The actual real-vector cost in the local weighted Hessian square. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- The explicit real-vector cost replaces the norm of the constructed
highest projection in the weighted square. -/
theorem weighted_hessian_cost (Y : Hessian) (hY : condition Y)
    (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0) (hu : ∑ s, u s = 0)
    (a : Vec) (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi)
    (x y m : ℝ) (hm : 0 < m) (hy : 0 ≤ y)
    (htx : ∀ s, -x ≤ t s) (huy : ∀ s, -y ≤ u s) (hxy : x + y ≤ 2) :
    0 ≤ (m / 6) * curvaturePairing t u Y Y +
      curvaturePairing t u Y (weightTensor a Z) / 6 +
      (‖a‖ ^ 2 * ((7 / 12) * (4 + y) * Z.squaredNorm -
        (5 / 4) * ∑ s, t s * (∑ b, ‖Z.matrix s b‖ ^ 2))) / (24 * m) := by
  have hsq := weighted_highestProjection_square Y (weightTensor a Z) hY
    t u x y m hm htx huy hxy
  have hcost := highestProjection_weight_cost t u ht hu x y htx huy hy hxy a Z hz hb
  have hdivide := div_le_div_of_nonneg_right hcost (show 0 ≤ 24 * m by positivity)
  linarith

/-- The cost estimate for a genuine Hessian derives its trace from Bianchi
and the Ricci commutator; no representation-theoretic projection is an input. -/
theorem local_weighted_hessian_cost (X : Hessian) (t u : Fin 3 → ℝ)
    (ht : ∑ s, t s = 0) (hu : ∑ s, u s = 0)
    (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0)
    (hcomm : ∀ i j b c, X i j b c - X j i b c =
      (1 / 2) * ∑ s, (1 + t s) * quaternionMatrix s i j *
        matrixAction s (Matrix.diagonal t) b c)
    (a : Vec) (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi)
    (x y m : ℝ) (hm : 0 < m) (hy : 0 ≤ y)
    (htx : ∀ s, -x ≤ t s) (huy : ∀ s, -y ≤ u s) (hxy : x + y ≤ 2) :
    0 ≤ (m / 6) * curvaturePairing t u (hessianRemainder X t) (hessianRemainder X t) +
      curvaturePairing t u (hessianRemainder X t) (weightTensor a Z) / 6 +
      (‖a‖ ^ 2 * ((7 / 12) * (4 + y) * Z.squaredNorm -
        (5 / 4) * ∑ s, t s * (∑ b, ‖Z.matrix s b‖ ^ 2))) / (24 * m) := by
  exact weighted_hessian_cost (hessianRemainder X t)
    (trace_subtracted_condition X t ht hmatrix
      (trace_eq_of_bianchi_commutator X t ht hmatrix hbianchi hcomm) hbianchi hcomm)
    t u ht hu a Z hz hb x y m hm hy htx huy hxy

end
end PositiveEinsteinFour.HighestHessian

end OAI
