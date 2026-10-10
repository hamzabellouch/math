import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! # Differentiation of the function argument of a moving linear map -/

open Filter
open scoped Topology
namespace RegularPointCoordinates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem moving_linear_difference_tendsto (T : ℝ → E →L[ℝ] F)
    (u : ℝ → E) {s : ℝ} {D : E}
    (hT : ContinuousAt (fun q : E × ℝ => T q.2 q.1) (D,s))
    (hu : HasDerivAt u D s) :
    Tendsto (fun t => (t-s)⁻¹ • (T t (u t)-T t (u s)))
      (𝓝[≠] s) (𝓝 (T s D)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] s) (𝓝 s) := nhdsWithin_le_nhds
  have hc := hT.tendsto.comp (hu.tendsto_slope.prodMk_nhds ht)
  simpa only [Function.comp_def,slope_def_module,map_smul,map_sub] using hc

end RegularPointCoordinates

end OAI
