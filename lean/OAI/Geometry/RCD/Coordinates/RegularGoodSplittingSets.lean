import OAI.Geometry.RCD.Coordinates.GoodSplittingSet
import OAI.Geometry.RCD.Metric.PointedCompactness
import OAI.Geometry.RCD.Coordinates.MeasuredCoordinates
import OAI.Geometry.RCD.Coordinates.MeasuredRescalingFromCoordinates
import OAI.Geometry.RCD.Coordinates.InitialHarmonicCoordinates
import OAI.Geometry.RCD.Coordinates.InitialSplittingConstruction

namespace OAI

/-! # Actual harmonic good sets at every sufficiently small regular scale -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_good_splitting_sets {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {p : X} (hp : IsRegular n p) {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) (hεt : ε ≤ t) :
    ∃ s : ℝ, 0 < s ∧ ∀ R : ℝ, 0 < R → R < s →
      ∃ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (v : X → Euclidean n) (U : Set X),
        -1 ≤ K*(5*R)^2 ∧
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*R) ε u v ∧
        IsCompact U ∧ U ⊆ closedBall p R ∧
        (hausdorff n X).real (ball p R \ U) ≤
          (fiveBallConstant n/t)*((n:ℝ)^2*ε*(hausdorff n X).real (ball p (2*R))) ∧
        ∀ x ∈ U, ∀ r : ℝ, 0 < r → r < R →
          FirstOrderSplittingOn (hausdorff n X) hX.quadratic x r t u v := by
  obtain ⟨s,hs,hinit⟩ := regular_initial_splitting_at_all_small_scales hX hn
    (hX.pointedRescalingPrecompactness hn p) hp
    (hX.measuredCoordinateInput.euclideanMeasuredRescalingConvergence hn p)
    hX.initialSplittingInput hε
  refine ⟨min s (min 1 (1/(25*(|K|+1)))),lt_min hs (lt_min zero_lt_one (by positivity)),?_⟩
  intro R hR hRs
  have hRs' : R < s := hRs.trans_le (min_le_left _ _)
  have hR1 : R ≤ 1 := (hRs.le.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hRK : R ≤ 1/(25*(|K|+1)) :=
    (hRs.le.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hm := (le_div_iff₀ (by positivity : 0 < 25*(|K|+1))).mp hRK
  have hsquare : R^2 ≤ R := by nlinarith
  have habs : |K| * (5*R)^2 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hsquare (abs_nonneg K)
    nlinarith
  have hcurv : -1 ≤ K*(5*R)^2 := by
    have hh := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg (5*R))
    linarith
  obtain ⟨u,v,huv⟩ := hinit R hR hRs'
  obtain ⟨U,hU,hUsub,hbad,hgood⟩ := hX.good_splitting_set hn p hR hcurv hε.le ht hεt huv
  exact ⟨u,v,U,hcurv,huv,hU,hUsub,hbad,hgood⟩

end RegularPointCoordinates

end

end OAI
