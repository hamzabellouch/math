import Mathlib

namespace OAI

/-! # A left difference quotient gives the left derivative -/

open Set Filter
open scoped Topology
namespace RegularPointCoordinates

theorem hasLeftDeriv_of_backward_quotient (F : ℝ → ℝ) (s c : ℝ)
    (h : Tendsto (fun t : ℝ => (F s-F (s-t))/t) (𝓝[>] (0:ℝ)) (𝓝 c)) :
    HasDerivWithinAt F c (Iio s) s := by
  have ht : Tendsto (fun t : ℝ => s-t) (𝓝[<] s) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [sub_self] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => s) (𝓝[<] s) (𝓝 s)).sub
          (show Tendsto (fun t : ℝ => t) (𝓝[<] s) (𝓝 s) from nhdsWithin_le_nhds))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < s-t
      exact sub_pos.mpr (show t < s from ht)
  apply (hasDerivWithinAt_iff_tendsto_slope' (show s ∉ Iio s by simp)).mpr
  apply (h.comp ht).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Function.comp_apply]
  rw [slope_def_field]
  rw [show s-(s-t)=t by ring]
  rw [show F s-F t=-(F t-F s) by ring, show s-t=-(t-s) by ring]
  simp only [div_neg,neg_div,neg_neg]

end RegularPointCoordinates

end OAI
