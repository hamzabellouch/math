import OAI.Analysis.LipschitzHilbert.Estimates.TopWeightIntegral

namespace OAI

/-! The source plane integral already has the exact top-weight mass.
The marked-path and conditional-average exponentials combine into a
fixed constant, independent of all packet and top scales. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem source_plane_weight_cost (T : SlopeBox) (K D cost : ℝ) (hK : 0 < K) :
    (((Real.exp 3*cost)*(Real.exp 1*Real.exp (2*D)))*
      (2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2*T.length*T.width =
    Real.exp (4+2*D)*cost*(∫ z, T.weight K D z ∂volume.prod volume) := by
  rw [T.integral_weight hK D,Real.exp_add,show (4:ℝ) = 3+1 by norm_num,Real.exp_add]
  ring

/-- The spatial estimate is exactly the weight integral required by the
finite-tree moment theorem; it has no residual area normalization. -/
theorem source_plane_bound_by_weight (T : SlopeBox) (K D cost I : ℝ) (hK : 0 < K)
    (h : I ≤ (((Real.exp 3*cost)*(Real.exp 1*Real.exp (2*D)))*
      (2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2*T.length*T.width) :
    I ≤ Real.exp (4+2*D)*cost*(∫ z, T.weight K D z ∂volume.prod volume) :=
  h.trans_eq (source_plane_weight_cost T K D cost hK)

end LipschitzHilbert

end

end OAI
