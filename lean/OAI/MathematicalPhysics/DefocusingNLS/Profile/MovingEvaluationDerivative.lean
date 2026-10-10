import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! # Differentiating a moving bounded observation

Only continuity in operator norm is needed for the moving observation; its
derivative is required on the single vector at the base point.
-/

open Filter Topology

namespace DefocusingNLS

theorem hasDerivAt_moving_observation
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ → V →L[ℝ] F) (u : ℝ → V) (t : ℝ) (v : V) (d : F)
    (hA : ContinuousAt A t) (hu : HasDerivAt u v t)
    (hd : HasDerivAt (fun s => A s (u t)) d t) :
    HasDerivAt (fun s => A s (u s)) (A t v + d) t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have h := (isBoundedBilinearMap_apply.continuous.tendsto
    (A t, v)).comp ((hA.tendsto.mono_left nhdsWithin_le_nhds).prodMk_nhds hu.tendsto_slope)
  have hs := h.add hd.tendsto_slope
  convert hs using 1
  ext s
  simp only [Function.comp_def, slope_def_module, map_smul, map_sub, smul_sub]
  abel

end DefocusingNLS

end OAI
