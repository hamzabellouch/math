import OAI.Geometry.RCD.Metric.MeasuredApproximation

namespace OAI

/-! # Initial harmonic coordinates at arbitrarily small regular scales -/

open Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem regular_initial_splitting_at_all_small_scales {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {p : X}
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular n p)
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff n X) n p)
    (hinitial : LocalInitialSplittingInput hX) {β : ℝ} (hβ : 0 < β) :
    ∃ s : ℝ, 0 < s ∧ ∀ r : ℝ, 0 < r → r < s →
      ∃ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2 * r) β u v := by
  obtain ⟨ε, hε, happly⟩ := hinitial hn β hβ
  obtain ⟨d, hd, happrox⟩ := regular_small_scale_measured_approximation hcompact hregular hmeasured
    (by norm_num : (0 : ℝ) < 16) hε
  let s := min d (min 1 (ε / (|K| + 1)))
  have hs : 0 < s := lt_min hd (lt_min zero_lt_one (div_pos hε (by positivity)))
  refine ⟨s, hs, ?_⟩
  intro r hr hrs
  have hrd : r < d := hrs.trans_le (min_le_left _ _)
  have hr1 : r ≤ 1 := hrs.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hre : r ≤ ε / (|K| + 1) := hrs.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbound : r * (|K| + 1) ≤ ε := (le_div_iff₀ (by positivity)).mp hre
  have hsquare : r ^ 2 ≤ r := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsquare (abs_nonneg K)
  have hK := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg r)
  have hcurv : -ε ≤ K * r ^ 2 := by nlinarith
  exact happly p r hr hcurv (happrox r hr hrd)

end RegularPointCoordinates

end

end OAI
