import OAI.MathematicalPhysics.DefocusingNLS.Profile.MovingSobolevEvaluation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevForcedEvaluation

namespace OAI

/-! # A strong Sobolev equation evaluated at moving physical points -/

open Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem hasDerivAt_sobolev_moving_point (k L : ℝ) (hk : 8 < k)
    (u : ℝ → FourierL2) (t : ℝ) (y : E) (v : FourierL2) (d : ℂ)
    (hu : HasDerivAt (fun s => lowerSobolevInclusion (u s)) v t)
    (hd : HasDerivAt (fun s => sobolevTorusFunction k (u s)
      (euclideanToTorus ((expandingRadius L t)⁻¹ • y))) d t) :
    HasDerivAt (fun s => sobolevTorusFunction k (u s)
      (euclideanToTorus ((expandingRadius L s)⁻¹ • y)))
      (d + (-((expandingRadius L t)⁻¹) / 2) •
        sobolevPhysicalDirectional k (u t) ((expandingRadius L t)⁻¹ • y) y) t := by
  let x := fun s => euclideanToTorus ((expandingRadius L s)⁻¹ • y)
  let A := fun s => (sobolevPointEvaluation (k - 2) (by linarith) (x s)).restrictScalars ℝ
  have hx : Continuous x := by
    have hc : Continuous (fun s => (expandingRadius L s)⁻¹) :=
      continuous_iff_continuousAt.mpr fun s => (hasDerivAt_expandingRadius_inv L s).continuousAt
    dsimp [x, euclideanToTorus]
    apply continuous_pi
    intro j
    change Continuous (fun s : ℝ =>
      (((expandingRadius L s)⁻¹ * y j : ℝ) : AddCircle (2 * Real.pi)))
    exact (AddCircle.continuous_mk' (2 * Real.pi)).comp (hc.mul continuous_const)
  have hA : Continuous A := by
    exact (ContinuousLinearMap.isEmbedding_restrictScalars ℝ).continuous.comp
      ((continuous_sobolevPointEvaluation (k - 2) (by linarith)).comp hx)
  have hAv : A t v = d := by
    have h := (A t).hasFDerivAt.comp_hasDerivAt t hu
    have h' : HasDerivAt (fun s => sobolevTorusFunction k (u s) (x t)) (A t v) t := by
      simpa only [Function.comp_def, A, ContinuousLinearMap.coe_restrictScalars',
        sobolevPointEvaluation_lowerInclusion k hk] using h
    exact h'.unique hd
  have hfixed : HasDerivAt (fun s => A s (lowerSobolevInclusion (u t)))
      ((-((expandingRadius L t)⁻¹) / 2) •
        sobolevPhysicalDirectional k (u t) ((expandingRadius L t)⁻¹ • y) y) t := by
    simpa only [A, x, ContinuousLinearMap.coe_restrictScalars',
      sobolevPointEvaluation_lowerInclusion k hk] using
        hasDerivAt_sobolev_expanding_point k L hk (u t) y t
  have h := hasDerivAt_moving_observation A (fun s => lowerSobolevInclusion (u s))
    t v _ hA.continuousAt hu hfixed
  simpa only [hAv, A, x, ContinuousLinearMap.coe_restrictScalars',
    sobolevPointEvaluation_lowerInclusion k hk] using h

end DefocusingNLS

end OAI
