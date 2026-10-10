import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyRegularizer
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

namespace OAI

/-! The compact correction makes every real exceptional energy space
below the threshold finite dimensional. The proof uses the actual
compact core operators, not a spectral finiteness assumption. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaEnergyPencil (z : ℂ) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  1-z • cubicThetaEnergyMass

theorem cubicThetaEnergyPencil_finite_ker {z : ℝ} (hz : 0≤z) (hz2 : z<2) :
    FiniteDimensional ℂ (cubicThetaEnergyPencil (z:ℂ)).ker := by
  obtain ⟨K,hK,hunit⟩ := cubicThetaEnergyPencil_compact_regularizer hz hz2
  let T := cubicThetaEnergyPencil (z:ℂ)
  let U : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace := T+K
  have hU : IsUnit U := hunit
  have hleft (u : cubicThetaGlobalEnergySpace) : Ring.inverse U (U u)=u := by
    change (Ring.inverse U*U) u=u
    rw [Ring.inverse_mul_cancel _ hU]
    rfl
  have hid : T.ker.subtypeL=(Ring.inverse U).comp (K.comp T.ker.subtypeL) := by
    apply ContinuousLinearMap.ext
    intro u
    have he : U u.val=K u.val := by
      change T u.val+K u.val=K u.val
      have hz : T (u : cubicThetaGlobalEnergySpace)=0 := u.property
      rw [hz,zero_add]
    change u.val=Ring.inverse U (K u.val)
    rw [← he,hleft]
  have hi : IsCompactOperator T.ker.subtypeL := by
    rw [hid]
    exact (hK.comp_clm T.ker.subtypeL).clm_comp (Ring.inverse U)
  have hc := hi.codRestrict (V:=T.ker) (fun u => u.property) T.isClosed_ker
  apply FiniteDimensional.of_isCompactOperator_id (𝕜:=ℂ)
  exact hc

end CubicFirstMoment

end

end OAI
