import OAI.Geometry.RCD.Coordinates.RegularLimitFiniteEuclidean
import OAI.Geometry.RCD.Metric.IsometricBallMeasure
import OAI.Geometry.RCD.Metric.PowerBallFullImage

namespace OAI

/-! # Full Euclidean neighborhoods in actual near-regular metric limits -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [ProperSpace Y]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]

include hX in
theorem regular_limit_euclidean_neighborhood (hn : 2 ≤ n) (hK : K ≤ 0)
    {o : X} (ho : IsRegular n o) {q : Y}
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hp : Tendsto p atTop (𝓝 o)) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -1 ≤ K*(4*r k)^2)
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (ε k) (V k)) :
    ∃ f : closedBall q (1/4:ℝ) → Euclidean n, Isometry f ∧
      f ⟨q,by simp⟩ = 0 ∧ ball (0:Euclidean n) (1/32) ⊆ range f := by
  obtain ⟨m,hmn,f,hf,-,hcompact,hzero⟩ :=
    hX.regular_limit_finite_euclidean hn hK ho p r ε V hp hr hr0 hε hcurv hV
  obtain ⟨Q,-,hQ⟩ := hX.regular_metric_limit_measure hn ho (by norm_num : (0:ℝ)<1/8)
    (by norm_num : (1/8:ℝ)≤5) p r ε V hp hr hr0 hε hV
  let μ := isometricBallMeasure (Q : Measure Y) q (1/4) f
  let : IsFiniteMeasure μ := isometricBallMeasure_finite (Q : Measure Y) q (1/4) f
  have hμ : ∀ᵐ x ∂μ, x ∈ range f := isometricBallMeasure_supported _ _ _ _ hf
  let q' : closedBall q (1/4:ℝ) := ⟨q,by simp⟩
  have hmass : ∀ y ∈ range f ∩ closedBall (0:Euclidean m) (1/32),
      ∀ t : ℝ, 0 < t → t ≤ 1/32 → μ.real (closedBall y t) = (t/(1/8))^n := by
    rintro y ⟨⟨x,rfl⟩,hy⟩ t ht hta
    have hxd : dist (x:Y) q ≤ 1/32 := by
      have he := hf.dist_eq x q'
      change dist (f x) (f q') = dist (x:Y) q at he
      rw [hzero] at he
      simpa only [mem_closedBall,he] using hy
    have he := isometricBallMeasure_closedBall (Q : Measure Y) f hf x t (by linarith)
    change μ.real (closedBall (f x) t) = _
    rw [Measure.real,he]
    exact (hQ x t ht (by linarith)).2
  have hmass0 : μ.real (closedBall (0:Euclidean m) (1/32)) = ((1/32)/(1/8):ℝ)^n := by
    have hh := hmass 0 ⟨⟨q',hzero⟩,by simp⟩ (1/32) (by norm_num) le_rfl
    exact hh
  have hmn' := euclidean_dimension_of_power_ball_mass μ hcompact.isClosed hμ hmn
    (by norm_num : (0:ℝ)<1/32) (by norm_num : (0:ℝ)<1/8)
    (by rw [hmass0]; positivity) hmass
  subst m
  have hopen : μ.real (ball (0:Euclidean n) (1/32)) = ((1/32)/(1/8):ℝ)^n := by
    have he := isometricBallMeasure_ball (Q : Measure Y) f hf q' (1/32) (by norm_num [q'])
    rw [hzero] at he
    rw [Measure.real,he]
    exact (hQ q (1/32) (by norm_num) (by simp; norm_num)).1
  refine ⟨f,hf,hzero,?_⟩
  exact ball_subset_of_power_ball_mass (by omega) μ hcompact.isClosed hμ
    (by norm_num) (by norm_num) hopen hmass

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
