import OAI.Geometry.RCD.Metric.LocalContractionAbsoluteContinuity

namespace OAI

/-! # Absolute continuity of the actual metric-law limit on the open ball -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem probability_restrict_absolutelyContinuous_of_local {n : ℕ}
    (Q : ProbabilityMeasure (Euclidean n)) {U : Set (Euclidean n)} (hU : MeasurableSet U)
    (hlocal : ∀ x ∈ U, ∃ R : ℝ, 0 < R ∧
      (Q : Measure (Euclidean n)).restrict (ball x R) ≪ volume) :
    (Q : Measure (Euclidean n)).restrict U ≪ volume := by
  classical
  have hl (x : U) := hlocal x x.2
  choose R hR hAC using hl
  let O := fun x : U => ball (x : Euclidean n) (R x)
  obtain ⟨T,hT,hcover⟩ := TopologicalSpace.isOpen_iUnion_countable O (fun _ => isOpen_ball)
  intro A hA
  rw [Measure.restrict_apply' hU]
  have hn (x : U) : (Q : Measure (Euclidean n)) (A ∩ O x)=0 := by
    have hh := hAC x hA
    simpa only [Measure.restrict_apply' measurableSet_ball] using hh
  have hsub : A ∩ U ⊆ ⋃ x ∈ T, A ∩ O x := by
    intro y hy
    have hc : y ∈ ⋃ x ∈ T, O x := by
      rw [hcover]
      exact mem_iUnion_of_mem ⟨y,hy.2⟩ (mem_ball_self (hR ⟨y,hy.2⟩))
    obtain ⟨x,hx,hxy⟩ := mem_iUnion₂.mp hc
    exact mem_iUnion₂.mpr ⟨x,hx,hy.1,hxy⟩
  exact measure_mono_null hsub ((measure_biUnion_null_iff hT).mpr (fun x _ => hn x))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_limit_absolutelyContinuous {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K ≤ 0)
    {S : ℝ} (hS : 0 < S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -ε k ≤ K*(r k)^2) (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (V k))
    (hfin : ∀ k, hausdorff n X (ball (p k) (S*r k)) ≠ ⊤)
    {Q : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto (fun k => normalizedBallPushforward (hausdorff n X)
      (p k) (r k) S (V k) (hfin k)) atTop (𝓝 Q))
    (hpositive : ∀ x ∈ ball (0 : Euclidean n) S, ∀ t : ℝ, 0 < t →
      0 < (Q : Measure (Euclidean n)).real (ball x t)) :
    (Q : Measure (Euclidean n)).restrict (ball 0 S) ≪ volume := by
  apply probability_restrict_absolutelyContinuous_of_local Q measurableSet_ball
  intro z hz
  obtain ⟨δ,hδ,hc⟩ := hX.metric_limit_local_contraction hn hK hS p r ε V hr hε hcurv
    hVm hV hfin hlim hpositive z hz
  exact ⟨δ/4,by positivity,local_contraction_absolutelyContinuous (by omega) Q z hδ hc⟩

end RegularPointCoordinates

end

end OAI
