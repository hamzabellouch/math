import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem momentum_hasDerivAt_zero_base {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    {c v : ℝ → E} {v' : E} (hG : DifferentiableAt ℝ G (c 0))
    (hc : HasDerivAt c 0 0) (hv : HasDerivAt v v' 0) :
    HasDerivAt (fun s => G (c s) (v s)) (G (c 0) v') 0 := by
  have hh₀ := hG.hasFDerivAt.comp_hasDerivAt (l := G) (f := c) 0 hc
  have hh : HasDerivAt (fun s => G (c s)) 0 0 := by
    convert hh₀ using 1 <;> (first | rfl | simp)
  simpa only [zero_apply,zero_add] using hh.clm_apply hv

 theorem zero_momentum_zero_velocity {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    {c v : ℝ → E} {v' : E} (hG : DifferentiableAt ℝ G (c 0))
    (hg : ∀ w : E, w ≠ 0 → 0 < G (c 0) w w)
    (hc : HasDerivAt c 0 0) (hv : HasDerivAt v v' 0)
    (hp : HasDerivAt (fun s => G (c s) (v s)) 0 0) : v' = 0 := by
  have hh := (momentum_hasDerivAt_zero_base hG hc hv).unique hp
  by_contra hn
  have hpos := hg v' hn
  rw [hh,zero_apply] at hpos
  exact (lt_irrefl 0) hpos

end
end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
