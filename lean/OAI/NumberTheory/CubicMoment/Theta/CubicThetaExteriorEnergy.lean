import OAI.NumberTheory.CubicMoment.Theta.CubicThetaExteriorIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyIntegralIdentities

namespace OAI

/-! The sharp exterior estimate extends by density to the actual closed
automorphic energy space. Its remainders are compact operators already
constructed from local Rellich compactness. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaExterior_energy {ε : ℝ} (hε : 0<ε) :
    ∃ (S R : Finset SL(2,Eisenstein)) (B : ℝ), 0≤B ∧
      ∀ u : cubicThetaGlobalEnergySpace,
    ‖cubicThetaGlobalInclusion u‖^2≤
      (1+ε)*‖cubicThetaGlobalEnergyGradient u‖^2+
      ‖cubicThetaCoreRestriction S 2 u‖^2+B*‖cubicThetaCoreRestriction R 2 u‖^2 := by
  obtain ⟨S,R,B,hB,h⟩ := cubicThetaExterior_integral hε
  refine ⟨S,R,B,hB,?_⟩
  let K : Set cubicThetaGlobalEnergySpace := {u | ‖cubicThetaGlobalInclusion u‖^2≤
    (1+ε)*‖cubicThetaGlobalEnergyGradient u‖^2+
      ‖cubicThetaCoreRestriction S 2 u‖^2+B*‖cubicThetaCoreRestriction R 2 u‖^2}
  have hK : IsClosed K := isClosed_le (by fun_prop) (by fun_prop)
  have ht : Set.range cubicThetaGlobalEnergyTestLinear⊆K := by
    rintro u ⟨F,rfl⟩
    change ‖cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)‖^2≤
      (1+ε)*‖cubicThetaGlobalEnergyGradient (cubicThetaGlobalEnergyTest F)‖^2+
      ‖cubicThetaCoreRestriction S 2 (cubicThetaGlobalEnergyTest F)‖^2+
      B*‖cubicThetaCoreRestriction R 2 (cubicThetaGlobalEnergyTest F)‖^2
    rw [cubicThetaGlobalInclusion_test_norm_sq,cubicThetaGlobalGradient_test_norm_sq,
      cubicThetaCoreRestriction_test_norm_sq,cubicThetaCoreRestriction_test_norm_sq]
    exact h F
  intro u
  exact closure_minimal ht hK (cubicThetaGlobalEnergyTestLinear_dense u)

end CubicFirstMoment

end

end OAI
