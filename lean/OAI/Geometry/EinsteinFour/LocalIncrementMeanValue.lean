import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! A mean-value bound requiring only local one-sided increment inequalities. -/
namespace PositiveEinsteinFour.Geometry
open Set Filter
open scoped Topology

theorem sub_le_of_local_increment (f : ℝ → ℝ) (a b C : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hlocal : ∀ x ∈ Ico a b, ∀ᶠ y in 𝓝[>] x,
      f y - f x ≤ C * (y-x)) :
    f b - f a ≤ C * (b-a) := by
  let B : ℝ → ℝ := fun x => f a + C * (x-a)
  have hB : Continuous B := continuous_const.add (continuous_const.mul
    (continuous_id.sub continuous_const))
  have hderiv (x : ℝ) : HasDerivAt B C x := by
    simpa only [mul_one,B,id_eq] using! (((hasDerivAt_id x).sub_const a).const_mul C).const_add (f a)
  have hbound := image_le_of_liminf_slope_right_le_deriv_boundary hf
    (show f a ≤ B a by simp [B]) hB.continuousOn
    (fun x _ => (hderiv x).hasDerivWithinAt) (fun x hx r hr => ?_)
  · have h := hbound ⟨hab,le_rfl⟩
    dsimp [B] at h
    linarith
  · apply Filter.Eventually.frequently
    filter_upwards [hlocal x hx,self_mem_nhdsWithin] with y hy hxy
    have hd : 0 < y-x := sub_pos.mpr hxy
    have hs : slope f x y ≤ C := by
      rw [slope_def_field]
      exact (div_le_iff₀ hd).mpr hy
    exact hs.trans_lt hr

end PositiveEinsteinFour.Geometry

end OAI
