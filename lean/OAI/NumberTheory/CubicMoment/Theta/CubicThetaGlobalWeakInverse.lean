import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalEnergy

namespace OAI

/-! Riesz representation supplies the global weak inverse of the
mass-plus-gradient form on its actual energy completion. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaGlobalWeakSolution (F : CubicThetaGlobalL2) : cubicThetaGlobalEnergySpace :=
  (InnerProductSpace.toDual ℂ cubicThetaGlobalEnergySpace).symm
    ((innerSL ℂ F).comp cubicThetaGlobalInclusion)

lemma cubicThetaGlobalWeakSolution_equation (F : CubicThetaGlobalL2)
    (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalWeakSolution F) v=inner ℂ F (cubicThetaGlobalInclusion v) :=
  InnerProductSpace.toDual_symm_apply

lemma cubicThetaGlobalWeakSolution_unique (F : CubicThetaGlobalL2)
    {u : cubicThetaGlobalEnergySpace}
    (hu : ∀ v, inner ℂ u v=inner ℂ F (cubicThetaGlobalInclusion v)) :
    u=cubicThetaGlobalWeakSolution F := by
  apply (InnerProductSpace.toDual ℂ cubicThetaGlobalEnergySpace).injective
  ext v
  simpa [cubicThetaGlobalWeakSolution] using hu v

lemma cubicThetaGlobalWeakSolution_bound (F : CubicThetaGlobalL2) :
    ‖cubicThetaGlobalWeakSolution F‖≤‖F‖ := by
  unfold cubicThetaGlobalWeakSolution
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖innerSL ℂ F‖*‖cubicThetaGlobalInclusion‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖F‖*1 := by
      rw [innerSL_apply_norm]
      exact mul_le_mul_of_nonneg_left cubicThetaGlobalInclusion_norm (_root_.norm_nonneg _)
    _ = _ := mul_one _

end CubicFirstMoment

end

end OAI
