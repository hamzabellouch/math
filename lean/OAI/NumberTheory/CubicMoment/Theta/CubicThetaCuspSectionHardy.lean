import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspLogSection

namespace OAI

/-! The sharp radial Hardy inequality for the actual cutoff of any
compact smooth cubic section in each arithmetic cusp. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspLogSection_lift_deriv (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) (z : ℂ) {v : ℝ} (hv : 0<v) :
    deriv (cubicThetaLogLift (cubicThetaCuspLogSection δ F z)) v=
      deriv (cubicThetaCuspCutoffSection δ F z) v := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hv] with w hw
  exact cubicThetaCuspLogSection_lift δ F z hw

theorem cubicThetaCuspSection_hardy (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) :
    (∫ v in Ioi (0:ℝ), ‖cubicThetaCuspCutoffSection δ F z v‖^2/v^3)≤
      ∫ v in Ioi (0:ℝ), ‖deriv (cubicThetaCuspCutoffSection δ F z) v‖^2/v := by
  have h := cubicTheta_radial_hardy
    ((cubicThetaCuspLogSection_contDiff δ F z).of_le (by simp))
    (cubicThetaCuspLogSection_compact δ F z)
  calc
    _ = ∫ v in Ioi (0:ℝ), ‖cubicThetaLogLift (cubicThetaCuspLogSection δ F z) v‖^2/v^3 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [cubicThetaCuspLogSection_lift δ F z hv]
    _ ≤ ∫ v in Ioi (0:ℝ), ‖deriv (cubicThetaLogLift (cubicThetaCuspLogSection δ F z)) v‖^2/v := h
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [cubicThetaCuspLogSection_lift_deriv δ F z hv]

end CubicFirstMoment

end

end OAI
