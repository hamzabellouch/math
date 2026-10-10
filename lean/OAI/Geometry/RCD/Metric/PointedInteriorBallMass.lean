import OAI.Geometry.RCD.Metric.MetricLawMass
import OAI.Geometry.RCD.Metric.ProbabilityClosedMass
import OAI.Geometry.RCD.Metric.RescaledBallVolume
import OAI.Geometry.RCD.Harmonic.PointedRadialDistance

namespace OAI

/-! # Positive interior mass of weak limits of the actual metric laws

Pointed density supplies an actual source ball. Bishop--Gromov controls
its normalized mass uniformly before taking any measured limit.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_law_interior_lower {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {S t : ℝ}
    (hS : 0 < S) (ht : 0 < t) (htS : t ≤ S) (z : Euclidean n) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : X) (r ε : ℝ), 0 < r →
      -1 ≤ K*(S*r)^2 → ‖z‖+3*ε+t < S → 2*ε ≤ t →
      ∀ V : X → Euclidean n, Measurable V →
        IsPointedApproximation p 0 r S ε V →
        ∀ hfin : hausdorff n X (ball p (S*r)) ≠ ⊤,
          c ≤ (normalizedBallPushforward (hausdorff n X) p r S V hfin :
            Measure (Euclidean n)).real (closedBall z (2*t)) := by
  obtain ⟨D,hD,hvol⟩ := hX.rescaled_ball_volume_factor hn (a := 1)
    (by norm_num) (div_pos ht hS) ((div_le_one hS).mpr htS)
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  refine ⟨D⁻¹,inv_pos.mpr hD0,?_⟩
  intro p r ε hr hcurv hroom hε V hVm hV hfin
  have hε0 : 0 ≤ ε := dist_nonneg.trans hV.1
  have hz : dist z 0 ≤ S-ε := by rw [dist_zero_right]; linarith
  obtain ⟨q,hq,hqz⟩ := hV.2.2 z hz
  have hqr := (abs_le.mp (pointed_radial_distance hr hS.le hV hq)).1
  have hnorm : ‖V q‖ ≤ ε+‖z‖ := by
    have hh := dist_triangle (V q) z 0
    simp only [dist_zero_right] at hh
    linarith
  have hqr' : dist q p/r ≤ ‖z‖+3*ε := by linarith
  have hsub : ball q (t*r) ⊆ ball p (S*r) := by
    apply Metric.ball_subset_ball'
    have hb := (div_le_iff₀ hr).mp hqr'
    nlinarith
  have hsource := pointed_source_ball_image hr hV hq hsub hqz
  have hsource' : ball q (t*r) ⊆ V ⁻¹' closedBall z (2*t) ∩ ball p (S*r) := by
    intro x hx
    exact ⟨closedBall_subset_closedBall (by linarith) (hsource hx).1,(hsource hx).2⟩
  have hpos : 0 < (hausdorff n X).real (ball p (S*r)) :=
    ENNReal.toReal_pos (hX.fullSupport p (S*r) (mul_pos hS hr)).ne' hfin
  apply normalizedBallPushforward_mass_lower _ p r S V hfin hpos hVm
    measurableSet_closedBall hsource' hD0
  have hh := hvol p (S*r) (mul_pos hS hr) hcurv q hq
  have he : (t/S)*(S*r)=t*r := by field_simp
  simpa only [he] using hh

theorem NoncollapsedRCD.metric_probability_limit_positive {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {S : ℝ} (hS : 0 < S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ᶠ k in atTop, -1 ≤ K*(S*r k)^2)
    (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (V k))
    (hfin : ∀ k, hausdorff n X (ball (p k) (S*r k)) ≠ ⊤)
    {Q : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto (fun k => normalizedBallPushforward (hausdorff n X)
      (p k) (r k) S (V k) (hfin k)) atTop (𝓝 Q))
    {z : Euclidean n} (hz : z ∈ ball 0 S) {b : ℝ} (hb : 0 < b) :
    0 < (Q : Measure (Euclidean n)).real (ball z b) := by
  have hz' : ‖z‖ < S := by simpa only [mem_ball,dist_zero_right] using hz
  let t := min (b/4) ((S-‖z‖)/4)
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have ht1 : t ≤ b/4 := min_le_left _ _
  have ht2 : t ≤ (S-‖z‖)/4 := min_le_right _ _
  have htS : t ≤ S := by nlinarith [norm_nonneg z]
  obtain ⟨c,hc,hbound⟩ := hX.metric_law_interior_lower hn hS ht htS z
  apply probability_ball_pos_of_closed_mass hlim (show 2*t < b by linarith) hc
  filter_upwards [hcurv,hε.eventually (Iio_mem_nhds (show (0:ℝ)<t/3 by positivity))]
    with k hk he
  exact hbound (p k) (r k) (ε k) (hr k) hk (by linarith)
    (by linarith) (V k) (hVm k) (hV k) (hfin k)

end RegularPointCoordinates

end

end OAI
