import OAI.Analysis.Cotype.CoefficientPowerGap
import OAI.Analysis.Cotype.KConvexCoordinateCriterion
import OAI.Analysis.Cotype.APNontrivialType
import OAI.Analysis.Cotype.TypeExtrapolation

namespace OAI

noncomputable section
universe u
namespace Cotype
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem kConvex_of_nontrivialType (h : NontrivialType X) : KConvex X := by
  obtain ⟨N, hN, C, hC, hC2, hgap⟩ := cube_coordinate_semigroup_power_gap h
  obtain ⟨K, hK, hbound⟩ := projectionLinearCoefficient_bound_of_power_gap hN hC hC2
  apply kConvex_iff_coordinate_firstCoefficient_bound.mpr
  refine ⟨K, hK, fun n f => ?_⟩
  exact hbound (PiLp 2 (fun _ : Cube n => X)) n coordinateExpectation
    coordinateExpectation_idempotent coordinateExpectation_commute
    coordinateExpectation_contracts (hgap n) f

theorem kConvex_of_AP_cotype_cotype [Nontrivial X] (hAP : ApproximationProperty X)
    (hX : FiniteCotype X) (hXd : FiniteCotype (X →L[ℝ] ℝ)) : KConvex X :=
  kConvex_of_nontrivialType (nontrivialType_of_AP_cotype_cotype hAP hX hXd)

theorem mainTarget_proved [Nontrivial X] : MainTarget X := by
  intro hAP
  exact ⟨forwardTarget_proved, fun ⟨hX, hXd⟩ => kConvex_of_AP_cotype_cotype hAP hX hXd⟩

end Cotype

end

end OAI
