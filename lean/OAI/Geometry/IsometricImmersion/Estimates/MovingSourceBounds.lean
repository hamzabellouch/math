import OAI.Geometry.IsometricImmersion.Comparison.ActualComparisonEnergy

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

theorem movingSourceNorm_le_of_pointwise_bound
    {f : Coord → ℝ} {xl xr a b speed t F : ℝ}
    (hspeed : 0 ≤ speed) (ht : t ∈ Icc a b)
    (horder : inwardLeft xl a speed t ≤ inwardRight xr a speed t)
    (hF : 0 ≤ F)
    (hbound : ∀ p ∈ shrinkingSlab xl xr a b speed, |f p| ≤ F) :
    movingSourceNorm xl xr a speed f t ≤ F*Real.sqrt (xr-xl) := by
  let l := inwardLeft xl a speed t
  let r := inwardRight xr a speed t
  have hlen : r-l ≤ xr-xl := by
    have hi : 0 ≤ speed*(t-a) := mul_nonneg hspeed (sub_nonneg.mpr ht.1)
    dsimp [l,r,inwardLeft,inwardRight]
    linarith
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := l) (b := r) (C := F^2) (f := fun x => f (coordinatePoint x t)^2) (by
      intro x hx
      have hx0 : x ∈ Ioc l r := by
        rw [uIoc_of_le (show l ≤ r from horder)] at hx
        exact hx
      have hb := hbound _ (point_mem_shrinkingSlab ht ⟨hx0.1.le,hx0.2⟩)
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hF).mpr hb)
  have hsquare : (∫ x in l..r, f (coordinatePoint x t)^2) ≤ F^2*(xr-xl) := by
    apply (le_abs_self _).trans
    apply hi.trans
    rw [abs_of_nonneg (sub_nonneg.mpr horder)]
    exact mul_le_mul_of_nonneg_left hlen (sq_nonneg F)
  have hsqrt := Real.sqrt_le_sqrt hsquare
  simpa only [movingSourceNorm,movingIntervalIntegral,l,r,
    Real.sqrt_mul (sq_nonneg F),Real.sqrt_sq hF] using hsqrt

theorem integrated_movingSourceNorm_le_of_pointwise_bound
    {f : Coord → ℝ} {xl xr a b speed F : ℝ}
    (hab : a ≤ b) (hspeed : 0 ≤ speed) (hF : 0 ≤ F)
    (horder : ∀ t ∈ Icc a b, inwardLeft xl a speed t ≤ inwardRight xr a speed t)
    (hbound : ∀ p ∈ shrinkingSlab xl xr a b speed, |f p| ≤ F) :
    (∫ t in a..b, movingSourceNorm xl xr a speed f t) ≤
      F*Real.sqrt (xr-xl)*(b-a) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := F*Real.sqrt (xr-xl))
    (f := movingSourceNorm xl xr a speed f) (by
      intro t ht
      have ht0 : t ∈ Ioc a b := by simpa only [uIoc_of_le hab] using ht
      have ht1 : t ∈ Icc a b := ⟨ht0.1.le,ht0.2⟩
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ movingSourceNorm xl xr a speed f t from Real.sqrt_nonneg _)]
      exact movingSourceNorm_le_of_pointwise_bound hspeed ht1 (horder t ht1) hF hbound)
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] using hi)

end SmoothLocal.Hyperbolic

end

end OAI
