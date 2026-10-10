import OAI.Geometry.RCD.Sobolev.LocalSlopeEventualBound

namespace OAI

/-! # Passing a scalar increment-rate limit to the local slope -/

open Set Filter Metric
open scoped Topology ENNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem localSlope_le_of_rate_limit {f : X → ℝ} {x : X} {R : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hR : Tendsto R (𝓝[>] 0) (𝓝 L))
    (hbound : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ y, dist x y=r → |f x-f y| ≤ R r*r) :
    (localSlope f x).toReal ≤ L := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have he := hR.eventually (Iio_mem_nhds (show L < L+ε by linarith))
  obtain ⟨δ,hδ,hall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hbound.and he)
  have hs : localSlope f x ≤ ENNReal.ofReal (L+ε) := by
    apply localSlope_le_of_eventually_increment
    filter_upwards [ball_mem_nhds x hδ] with y hy
    by_cases hxy : x=y
    · subst y
      simp only [sub_self,abs_zero,dist_self,mul_zero,le_refl]
    · have hd : 0 < dist x y := dist_pos.mpr hxy
      have hyδ : dist x y < δ := by simpa only [mem_ball,dist_comm] using hy
      obtain ⟨hb,hr⟩ := hall ⟨hd,hyδ⟩
      exact (hb y rfl).trans (mul_le_mul_of_nonneg_right hr.le hd.le)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hs).trans_eq
    (ENNReal.toReal_ofReal (by linarith))

end RegularPointCoordinates

end OAI
