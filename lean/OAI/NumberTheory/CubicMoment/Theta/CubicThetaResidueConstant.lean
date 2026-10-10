import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantModeResidue

namespace OAI

/-! Numerical normalization of the computed principal constant-mode residue. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicTheta_constant_residue_coefficient :
    (2*Real.pi/(3*Real.sqrt 3):ℂ)*
      ((principalThetaConstant/(residueHeckeScale 1:ℂ))/(4*principalIdealZeta 2))=
        (Real.pi:ℂ)^2/(54*principalIdealZeta 2) := by
  rw [cubicTheta_principalZeta_residue_value]
  have hroot : (Real.sqrt 3:ℂ)^2=3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hn : (Real.sqrt 3:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  field_simp
  ring_nf
  rw [hroot]
  ring

theorem cubicThetaConstantModeContinuation_residue_explicit {v : ℝ} (hv : 0<v) :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaConstantModeContinuation v s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (((Real.pi:ℂ)^2/(54*principalIdealZeta 2))*(v:ℂ)^(2/3:ℂ))) := by
  simpa only [cubicTheta_constant_residue_coefficient] using
    cubicThetaConstantModeContinuation_residue hv

end CubicFirstMoment

end

end OAI
