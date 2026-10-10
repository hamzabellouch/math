import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

namespace OAI

/-! # Differentiating a strongly continuous family on a varying vector -/

open Filter Set Topology

namespace DefocusingNLS

theorem hasDerivWithinAt_strong_apply
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A : ℝ → V →L[ℝ] W) (v : ℝ → V) (dv : V) (w : W)
    (hA : Continuous (fun p : ℝ × V => A p.1 p.2))
    (hv : HasDerivWithinAt v dv (Ici 0) 0)
    (hw : HasDerivWithinAt (fun t => A t (v 0)) w (Ici 0) 0) :
    HasDerivWithinAt (fun t => A t (v t)) (w + A 0 dv) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hv hw ⊢
  have ht : Tendsto (fun t : ℝ => t) (𝓝[Ici 0 \ {0}] 0) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hlim := hw.add ((hA.tendsto (0, dv)).comp (ht.prodMk_nhds hv))
  apply hlim.congr'
  filter_upwards [] with t
  simp only [Function.comp_apply, slope_def_module, sub_zero, map_smul, map_sub]
  module

end DefocusingNLS

end OAI
