import OAI.Geometry.RCD.Metric.MetricBallLaw
import OAI.Geometry.RCD.Metric.EuclideanPairCompactness
import OAI.Geometry.RCD.Transport.PointedPlanSupport

namespace OAI

/-! # Weak limits of the original normalized ball laws on a proper metric target -/

open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [ProperSpace Y] [SeparableSpace Y]
  {q : Y}

theorem metric_ball_law_subsequence {S : ℝ} (hS : 0 ≤ S)
    (μ : Measure X) (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hr : ∀ k, 0 < r k) (hε1 : ∀ k, ε k ≤ 1) (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) S (ε k) (V k))
    (hfin : ∀ k, μ (ball (p k) (S*r k)) ≠ ⊤)
    (hpos : ∀ k, 0 < μ.real (ball (p k) (S*r k))) :
    ∃ ν : ProbabilityMeasure (Y), ∃ α : ℕ → ℕ, StrictMono α ∧
      Tendsto (fun k => metricBallLaw μ (p (α k)) (r (α k)) S (V (α k)) (hfin (α k)))
        atTop (𝓝 ν) ∧
      ∀ᵐ z ∂(ν : Measure (Y)), z ∈ closedBall q (S+2) := by
  let P := fun k => metricBallLaw μ (p k) (r k) S (V k) (hfin k)
  let A := closedBall q (S+2)
  have hA : IsCompact A := isCompact_closedBall _ _
  have hsupport (k : ℕ) : ∀ᵐ z ∂(P k : Measure (Y)), z ∈ A := by
    filter_upwards [metricBallLaw_supported μ (p k) (hr k) hS
      (V k) (hVm k) (hV k) (hfin k) (hpos k)] with z hz
    exact closedBall_subset_closedBall (by linarith [hε1 k]) hz
  have hnull (k : ℕ) : (P k : Measure (Y)) Aᶜ=0 := ae_iff.mp (hsupport k)
  have htight : IsTightMeasureSet {((ν : ProbabilityMeasure (Y)) :
      Measure (Y)) | ν ∈ range P} := by
    apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
    intro η hη
    refine ⟨A,hA,?_⟩
    rintro τ ⟨ν,⟨k,rfl⟩,rfl⟩
    exact (hnull k).le.trans hη.le
  obtain ⟨ν,_,α,hα,hlim⟩ := (isCompact_closure_of_isTightMeasureSet htight).tendsto_subseq
    (fun k => subset_closure (mem_range_self k))
  refine ⟨ν,α,hα,hlim,?_⟩
  apply ae_iff.mpr
  change (ν : Measure (Y)) Aᶜ=0
  have hh := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hA.isClosed.isOpen_compl
  have he : (fun k => (P (α k) : Measure (Y)) Aᶜ)=fun _ => 0 :=
    funext (fun k => hnull (α k))
  simpa only [Function.comp_def,he,liminf_const,le_zero_iff] using hh

omit [ProperSpace Y] [SeparableSpace Y] in
theorem metric_ball_law_limit_support {S : ℝ} (hS : 0 ≤ S)
    (μ : Measure X) (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0)) (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) S (ε k) (V k))
    (hfin : ∀ k, μ (ball (p k) (S*r k)) ≠ ⊤)
    (hpos : ∀ k, 0 < μ.real (ball (p k) (S*r k)))
    {ν : ProbabilityMeasure (Y)}
    (hlim : Tendsto (fun k => metricBallLaw μ (p k) (r k) S (V k) (hfin k))
      atTop (𝓝 ν)) :
    ∀ᵐ z ∂(ν : Measure (Y)), z ∈ closedBall q S := by
  have hb (j : ℕ) : ∀ᵐ z ∂(ν : Measure (Y)),
      z ∈ closedBall q (S+1/((j:ℝ)+1)) := by
    apply weak_limit_ae_closed _ hlim isClosed_closedBall
    filter_upwards [hε.eventually (Iio_mem_nhds
      (show (0:ℝ)<(1/((j:ℝ)+1))/2 by positivity))] with k hk
    filter_upwards [metricBallLaw_supported μ (p k) (hr k) hS
      (V k) (hVm k) (hV k) (hfin k) (hpos k)] with z hz
    exact closedBall_subset_closedBall (by linarith) hz
  filter_upwards [ae_all_iff.mpr hb] with z hz
  change dist z q ≤ S
  have ht : Tendsto (fun j : ℕ => S+1/((j:ℝ)+1)) atTop (𝓝 S) := by
    simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add S
  exact ge_of_tendsto ht (Eventually.of_forall hz)

end RegularPointCoordinates

end

end OAI
