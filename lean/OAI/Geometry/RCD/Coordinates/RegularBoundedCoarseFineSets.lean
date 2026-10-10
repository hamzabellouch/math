import OAI.Geometry.RCD.Coordinates.RegularGoodCoordinateSetsBounded
import OAI.Geometry.RCD.Coordinates.FlatSplittingApproximation
import OAI.Geometry.RCD.Coordinates.MeasuredCoordinates
import OAI.Geometry.RCD.Metric.PointedCompactness

namespace OAI

/-! # Coarse and fine charts for the same actual harmonic family -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_bounded_coarse_fine_sets {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hpublished : LocalAlmostSplittingInput hX) {p : X} (hp : IsRegular n p)
    {η ζ : ℝ} (hη : 0 < η) (hζ : 0 < ζ) :
    ∃ t s : ℝ, 0 < t ∧ t ≤ 1 ∧ 0 < s ∧ ∀ R : ℝ, 0 < R → R < s →
      ∃ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (v : X → Euclidean n) (U : Set X),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*R) t u v ∧
        IsCompact U ∧ U ⊆ closedBall p R ∧
        (hausdorff n X).real (ball p R \ U) ≤ ζ*(hausdorff n X).real (ball p R) ∧
        IsPointedApproximation p 0 (R/8) (1/2) (η/4)
          (fun x => (R/8)⁻¹ • (v x-v p)) ∧
        ∀ x ∈ U, ∀ r : ℝ, 0 < r → r < R/16 →
          IsPointedApproximation x 0 r (1/16) η (fun z => r⁻¹ • (v z-v x)) := by
  obtain ⟨τ,β,hτ,hβ,hcoarse⟩ := hX.flat_splitting_coordinates hn hX.measuredCoordinateInput
    (show 0 < η/4 by positivity)
  obtain ⟨t,s,ht,htsmall,hs,hsets⟩ := hX.regular_good_coordinate_sets_bounded
    hn hpublished hp hη hζ (lt_min hβ zero_lt_one)
  have htβ : t ≤ β := htsmall.trans (min_le_left _ _)
  have ht1 : t ≤ 1 := htsmall.trans (min_le_right _ _)
  obtain ⟨d,hd,hflat⟩ := regular_small_scale_approximation
    (hX.pointedRescalingPrecompactness hn p) hp (show (0:ℝ)<2 by norm_num) hτ
  refine ⟨t,min s (8*d),ht,ht1,lt_min hs (by positivity),?_⟩
  intro R hR hRs
  obtain ⟨u,v,U,hcurv,hsplit,hU,hUsub,hbad,hfine⟩ := hsets R hR (hRs.trans_le (min_le_left _ _))
  have hr : 0 < R/8 := by positivity
  have hcurvr : -β ≤ K*(R/8)^2 := by
    by_cases hK : 0 ≤ K
    · exact (neg_nonpos.mpr hβ.le).trans (mul_nonneg hK (sq_nonneg _))
    · have hsquare : (R/8)^2 ≤ R^2 := by nlinarith only [sq_nonneg R]
      have hm := mul_le_mul_of_nonpos_left hsquare (le_of_lt (lt_of_not_ge hK))
      exact (neg_le_neg htβ).trans (hcurv.trans hm)
  have hsplit' : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16*(R/8)) β u v := by
    simpa only [show 16*(R/8)=2*R by ring] using hsplit.mono_error _ _ ht.le htβ
  have hc := hcoarse p (R/8) hr hcurvr u v hsplit'
    (hflat (R/8) hr (by linarith only [hRs.trans_le (min_le_right _ _)]))
  exact ⟨u,v,U,hsplit,hU,hUsub,hbad,hc,hfine⟩

end RegularPointCoordinates

end

end OAI
