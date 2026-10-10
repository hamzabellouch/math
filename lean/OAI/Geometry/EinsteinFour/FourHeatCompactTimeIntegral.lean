import OAI.Geometry.EinsteinFour.FourHeatGaussianEquation
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! Differentiating a four-dimensional compactly supported pairing at
positive time. The domination is proved from compactness, not assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric MeasureTheory
open scoped Topology

noncomputable section

theorem fourHeat_compact_time_integral
    (F F' : ℝ → FourSpace → ℝ) (K : Set FourSpace) (hK : IsCompact K)
    (hF : ∀ t > 0, Continuous (F t))
    (hF' : ContinuousOn (Function.uncurry F') (Ioi (0 : ℝ) ×ˢ univ))
    (hs : ∀ t > 0, ∀ x ∉ K, F t x = 0)
    (hs' : ∀ t > 0, ∀ x ∉ K, F' t x = 0)
    (hd : ∀ t > 0, ∀ x, HasDerivAt (fun s => F s x) (F' t x) t)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, F s x) (∫ x, F' t x) t := by
  have hI (s : ℝ) (hs : s ∈ closedBall t (t / 2)) : 0 < s := by
    have habs : |s - t| ≤ t / 2 := by simpa only [mem_closedBall, Real.dist_eq] using hs
    have := (abs_le.mp habs).1
    linarith
  have hprod : closedBall t (t / 2) ×ˢ K ⊆ Ioi (0 : ℝ) ×ˢ univ :=
    fun z hz => ⟨hI z.1 hz.1, mem_univ _⟩
  have hcompact := (isCompact_closedBall t (t / 2)).prod hK
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image (hF'.mono hprod).norm
  let b : FourSpace → ℝ := K.indicator (fun _ => max C 0)
  have hb : Integrable b := by
    exact (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  have hbound : ∀ x, ∀ s ∈ ball t (t / 2), ‖F' s x‖ ≤ b x := by
    intro x s hsball
    by_cases hx : x ∈ K
    · change ‖F' s x‖ ≤ K.indicator (fun _ => max C 0) x
      rw [indicator_of_mem hx]
      exact (hC ⟨(s, x), ⟨ball_subset_closedBall hsball, hx⟩, rfl⟩).trans (le_max_left _ _)
    · change ‖F' s x‖ ≤ K.indicator (fun _ => max C 0) x
      rw [indicator_of_notMem hx, hs' s (hI s (ball_subset_closedBall hsball)) x hx,
        norm_zero]
  have hFc : HasCompactSupport (F t) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (hs t ht x hn)
  have hF't : Continuous (F' t) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hF'.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      (show (t, x) ∈ Ioi (0 : ℝ) ×ˢ univ from ⟨ht, mem_univ x⟩))).comp
      (continuousAt_const.prodMk continuousAt_id)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds t (by positivity))
    (by filter_upwards [Ioi_mem_nhds ht] with s hs; exact (hF s hs).aestronglyMeasurable)
    ((hF t ht).integrable_of_hasCompactSupport hFc) hF't.aestronglyMeasurable
    (Eventually.of_forall hbound) hb
    (Eventually.of_forall fun x s hsball => hd s (hI s (ball_subset_closedBall hsball)) x)).2

end
end PositiveEinsteinFour.Geometry

end OAI
