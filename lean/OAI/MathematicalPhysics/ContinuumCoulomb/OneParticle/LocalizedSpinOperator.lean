import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedTensorResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneElectronComplexLaplacian

namespace OAI

/-! Actual one-body differential residual of each corrected spatial-spin mode. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem localizedSpinMode_C2 (freq : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (j : Fin ((2*m+1)+1)) (s : Fin 2) : ContDiff ℝ 2 (fun x => localizedSpinMode freq u j x s) := by
  have hf : ContDiff ℝ 2 (correctedLocalizedMode freq u ((HubbardGlobal.siteModes m).symm j).1) :=
    (localizedLinearOrbital_C7 freq u (correctedLocalizedCoefficients u _)).of_le (by norm_num)
  by_cases hs : s=((HubbardGlobal.siteModes m).symm j).2
  · simpa only [localizedSpinMode,realSpinOrbital,hs,ite_true,Function.comp_def,
      Complex.ofRealCLM_apply] using Complex.ofRealCLM.contDiff.comp hf
  · simpa only [localizedSpinMode,realSpinOrbital,hs,ite_false] using
      (contDiff_const : ContDiff ℝ 2 (fun _ : Position => (0:ℂ)))

theorem localizedSpinResidual_operator {rho freq : ℝ} (hrelation : freq^2 = 4*Real.pi*rho)
    (H S scale : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (j : Fin ((2*m+1)+1)) (s : Fin 2) (x : Position) :
    localizedSpinResidual rho H S freq scale u j x s =
      (-1/2:ℂ)*positionComplexLaplacian (fun y => localizedSpinMode freq u j y s) x+
      (manufacturedSlabPotential rho H S freq scale u x:ℂ)*localizedSpinMode freq u j x s-
      (((-1/2:ℝ)+freq/2):ℂ)*localizedSpinMode freq u j x s := by
  by_cases hs : s=((HubbardGlobal.siteModes m).symm j).2
  · simpa only [localizedSpinResidual,localizedSpinMode,realSpinOrbital,hs,ite_true] using
      correctedManufacturedResidual_complex_laplacian hrelation H S scale u
        ((HubbardGlobal.siteModes m).symm j).1 x
  · simp [localizedSpinResidual,localizedSpinMode,realSpinOrbital,hs,
      positionComplexLaplacian,positionComplexPartial]

end ContinuumCoulomb

end

end OAI
