import OAI.Geometry.RCD.Metric.MeasuredBallLaw
import OAI.Geometry.RCD.Coordinates.NormalizedLawCompression
import OAI.Geometry.RCD.Harmonic.PointedRadialDistance
import OAI.Geometry.RCD.Metric.EuclideanPairCompactness
import OAI.Geometry.RCD.Transport.PointedPlanSupport

namespace OAI

/-! # Compactness of the actual laws of metric approximation maps

No measured approximation or identification of the limiting measure is
assumed. The laws retain the original ball and its exact normalization.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem normalizedBallPushforward_supported {n : ℕ} (μ : Measure X)
    (p : X) {r S ε : ℝ} (hr : 0 < r) (hS : 0 ≤ S)
    (V : X → Euclidean n) (hVm : Measurable V)
    (hV : IsPointedApproximation p 0 r S ε V)
    (hfin : μ (ball p (S*r)) ≠ ⊤) (hpos : 0 < μ.real (ball p (S*r))) :
    ∀ᵐ z ∂(normalizedBallPushforward μ p r S V hfin : Measure (Euclidean n)),
      z ∈ closedBall 0 (S+2*ε) := by
  let : Nonempty X := ⟨p⟩
  let : IsFiniteMeasure (μ.restrict (ball p (S*r))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  have hn : μ.restrict (ball p (S*r)) ≠ 0 := by
    intro he
    have hh := congrArg (fun ν : Measure X => ν.real univ) he
    simp [Measure.real] at hh
    exact hpos.ne' hh
  change ∀ᵐ z ∂((normalizedProbabilityLaw (μ.restrict (ball p (S*r)))).map V :
      Measure (Euclidean n)), z ∈ closedBall 0 (S+2*ε)
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff hVm.aemeasurable measurableSet_closedBall).mpr
  filter_upwards [normalized_restriction_ae_mem μ measurableSet_ball hn] with x hx
  have hrad := (abs_le.mp (pointed_radial_distance hr hS hV hx.le)).2
  have hdist : dist x p/r < S := (div_lt_iff₀ hr).mpr hx
  simpa only [mem_closedBall,dist_zero_right] using (show ‖V x‖ ≤ S+2*ε by linarith)

theorem pointed_probability_subsequence {n : ℕ} {S : ℝ} (hS : 0 ≤ S)
    (μ : Measure X) (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε1 : ∀ k, ε k ≤ 1) (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (V k))
    (hfin : ∀ k, μ (ball (p k) (S*r k)) ≠ ⊤)
    (hpos : ∀ k, 0 < μ.real (ball (p k) (S*r k))) :
    ∃ ν : ProbabilityMeasure (Euclidean n), ∃ α : ℕ → ℕ, StrictMono α ∧
      Tendsto (fun k => normalizedBallPushforward μ (p (α k)) (r (α k)) S (V (α k)) (hfin (α k)))
        atTop (𝓝 ν) ∧
      ∀ᵐ z ∂(ν : Measure (Euclidean n)), z ∈ closedBall 0 (S+2) := by
  let P := fun k => normalizedBallPushforward μ (p k) (r k) S (V k) (hfin k)
  let A := closedBall (0 : Euclidean n) (S+2)
  have hA : IsCompact A := isCompact_closedBall _ _
  have hsupport (k : ℕ) : ∀ᵐ z ∂(P k : Measure (Euclidean n)), z ∈ A := by
    filter_upwards [normalizedBallPushforward_supported μ (p k) (hr k) hS
      (V k) (hVm k) (hV k) (hfin k) (hpos k)] with z hz
    exact closedBall_subset_closedBall (by linarith [hε1 k]) hz
  have hnull (k : ℕ) : (P k : Measure (Euclidean n)) Aᶜ=0 := ae_iff.mp (hsupport k)
  have htight : IsTightMeasureSet {((ν : ProbabilityMeasure (Euclidean n)) :
      Measure (Euclidean n)) | ν ∈ range P} := by
    apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
    intro η hη
    refine ⟨A,hA,?_⟩
    rintro τ ⟨ν,⟨k,rfl⟩,rfl⟩
    exact (hnull k).le.trans hη.le
  obtain ⟨ν,_,α,hα,hlim⟩ := (isCompact_closure_of_isTightMeasureSet htight).tendsto_subseq
    (fun k => subset_closure (mem_range_self k))
  refine ⟨ν,α,hα,hlim,?_⟩
  apply ae_iff.mpr
  change (ν : Measure (Euclidean n)) Aᶜ=0
  have hh := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hA.isClosed.isOpen_compl
  have he : (fun k => (P (α k) : Measure (Euclidean n)) Aᶜ)=fun _ => 0 :=
    funext (fun k => hnull (α k))
  simpa only [Function.comp_def,he,liminf_const,le_zero_iff] using hh

theorem pointed_probability_limit_support {n : ℕ} {S : ℝ} (hS : 0 ≤ S)
    (μ : Measure X) (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0)) (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (V k))
    (hfin : ∀ k, μ (ball (p k) (S*r k)) ≠ ⊤)
    (hpos : ∀ k, 0 < μ.real (ball (p k) (S*r k)))
    {ν : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto (fun k => normalizedBallPushforward μ (p k) (r k) S (V k) (hfin k))
      atTop (𝓝 ν)) :
    ∀ᵐ z ∂(ν : Measure (Euclidean n)), z ∈ closedBall 0 S := by
  have hb (j : ℕ) : ∀ᵐ z ∂(ν : Measure (Euclidean n)),
      z ∈ closedBall 0 (S+1/((j:ℝ)+1)) := by
    apply weak_limit_ae_closed _ hlim isClosed_closedBall
    filter_upwards [hε.eventually (Iio_mem_nhds
      (show (0:ℝ)<(1/((j:ℝ)+1))/2 by positivity))] with k hk
    filter_upwards [normalizedBallPushforward_supported μ (p k) (hr k) hS
      (V k) (hVm k) (hV k) (hfin k) (hpos k)] with z hz
    exact closedBall_subset_closedBall (by linarith) hz
  filter_upwards [ae_all_iff.mpr hb] with z hz
  change dist z 0 ≤ S
  have ht : Tendsto (fun j : ℕ => S+1/((j:ℝ)+1)) atTop (𝓝 S) := by
    simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add S
  exact ge_of_tendsto ht (Eventually.of_forall hz)

end RegularPointCoordinates

end

end OAI
