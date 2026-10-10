import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real

namespace OAI

/-! # Transfer of a scalar limit through the proved cutoff error -/

open Filter
open scoped Topology
namespace RegularPointCoordinates

theorem tendsto_of_abs_cutoff_error {ι : Type*} {l : Filter ι}
    {f g e : ι → ℝ} {a : ℝ} (hg : Tendsto g l (𝓝 a)) (he : Tendsto e l (𝓝 0))
    (hb : ∀ᶠ i in l, |f i-g i| ≤ e i) : Tendsto f l (𝓝 a) := by
  have hz : Tendsto (fun i => f i-g i) l (𝓝 0) :=
    squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hb) he
  simpa only [sub_add_cancel,zero_add] using hz.add hg

end RegularPointCoordinates

end OAI
