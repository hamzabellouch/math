import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerTorus
import Mathlib.Analysis.Calculus.FDeriv.Linear

namespace OAI

/-! # Pointwise evaluation of the forced strong Sobolev equation -/

namespace DefocusingNLS

theorem sobolevPointEvaluation_lowerInclusion (k : ℝ) (hk : 8 < k)
    (x : SchrodingerTorus) (f : FourierL2) :
    sobolevPointEvaluation (k - 2) (by linarith) x (lowerSobolevInclusion f) =
      sobolevTorusFunction k f x := by
  rw [← sobolevTorusFunction_apply, sobolevTorusFunction_lower_inclusion]

theorem sobolevPointEvaluation_lowerGenerator (k : ℝ) (hk : 8 < k)
    (x : SchrodingerTorus) (f : FourierL2) :
    sobolevPointEvaluation (k - 2) (by linarith) x (lowerSobolevGenerator f) =
      Complex.I * torusFourierLaplacian k f x := by
  simp only [torusFourierLaplacian, sobolevTorusFunction_apply (k - 2) (by linarith), map_smul,
    smul_eq_mul]
  simp [← mul_assoc]

theorem hasDerivAt_forcedTorusFunction (k : ℝ) (hk : 8 < k)
    (u : ℝ → FourierL2) (t : ℝ) (x : SchrodingerTorus)
    (α β : ℂ) (g : FourierL2)
    (hu : HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (α • lowerSobolevInclusion (u t) + β • lowerSobolevGenerator (u t) +
        lowerSobolevInclusion g) t) :
    HasDerivAt (fun s => sobolevTorusFunction k (u s) x)
      (α * sobolevTorusFunction k (u t) x +
        β * (Complex.I * torusFourierLaplacian k (u t) x) + sobolevTorusFunction k g x) t := by
  let E := sobolevPointEvaluation (k - 2) (by linarith) x
  have h := (E.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hu
  have he : E (α • lowerSobolevInclusion (u t) + β • lowerSobolevGenerator (u t) +
        lowerSobolevInclusion g) =
      α * sobolevTorusFunction k (u t) x +
        β * (Complex.I * torusFourierLaplacian k (u t) x) + sobolevTorusFunction k g x := by
    simp only [map_add, map_smul, smul_eq_mul, E,
      sobolevPointEvaluation_lowerInclusion k hk, sobolevPointEvaluation_lowerGenerator k hk]
  simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', E,
    sobolevPointEvaluation_lowerInclusion k hk] using h.congr_deriv he

end DefocusingNLS

end OAI
