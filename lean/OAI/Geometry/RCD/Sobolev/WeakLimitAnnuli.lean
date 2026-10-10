import OAI.Geometry.RCD.Sobolev.EuclideanLawLocalizedTests
import OAI.Geometry.RCD.Metric.FiniteMeasureClosedBound

namespace OAI

/-! # Vanishing annular mass for weak Euclidean probability limits -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem vanishing_annuli_of_weak_limit {n : ℕ} {ρ : ℝ}
    (hρ : 0<ρ) {ν : ℕ → ProbabilityMeasure (Euclidean n)}
    {Q : ProbabilityMeasure (Euclidean n)} (hν : Tendsto ν atTop (𝓝 Q))
    (hnull : (Q : Measure (Euclidean n)) (sphere 0 ρ)=0) :
    ∀ η : ℝ, 0<η → ∃ δ : ℝ, 0<δ ∧ δ<ρ ∧ ∀ᶠ k in atTop,
      (ν k : Measure (Euclidean n)).real (closedBall 0 (ρ+δ) \ ball 0 (ρ-δ))<η := by
  let q : ℕ → ℝ := fun m => ρ/((m+2:ℕ):ℝ)
  have hqpos (m : ℕ) : 0<q m := div_pos hρ (by positivity)
  have hqlt (m : ℕ) : q m<ρ := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have hm : (1:ℝ)<((m+2:ℕ):ℝ) := by norm_cast; omega
    nlinarith
  have hq : Tendsto q atTop (𝓝 0) := by
    simpa only [q,div_eq_mul_inv,Function.comp_apply,one_mul,mul_zero] using
      (tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2)).const_mul ρ
  let A := fun m => closedBall (0:Euclidean n) (ρ+q m) \ ball 0 (ρ-q m)
  have hAm (m : ℕ) : MeasurableSet (A m) := measurableSet_closedBall.diff measurableSet_ball
  have hlim : ∀ z, Tendsto (fun m => (A m).indicator (fun _ => (1:ℝ)) z) atTop
      (𝓝 ((sphere (0:Euclidean n) ρ).indicator (fun _ => (1:ℝ)) z)) := by
    intro z
    by_cases hz : ‖z‖=ρ
    · have hzA (m : ℕ) : z∈A m := by
        simp only [A,Set.mem_sdiff,mem_closedBall,mem_ball,dist_zero_right,not_lt,hz]
        exact ⟨by linarith [hqpos m],by linarith [hqpos m]⟩
      have hzs : z∈sphere (0:Euclidean n) ρ := by simpa only [mem_sphere,dist_zero_right] using hz
      simp only [indicator_of_mem (hzA _),indicator_of_mem hzs]
      exact tendsto_const_nhds
    · have hpos : 0 < |‖z‖-ρ| := abs_pos.mpr (sub_ne_zero.mpr hz)
      have he : ∀ᶠ m in atTop, z∉A m := by
        filter_upwards [hq.eventually (Iio_mem_nhds hpos)] with m hm
        simp only [A,Set.mem_sdiff,mem_closedBall,mem_ball,dist_zero_right,not_and,not_lt]
        intro hh
        have hcases := lt_or_gt_of_ne hz
        rcases hcases with hlt | hgt
        · rw [abs_of_neg (sub_neg.mpr hlt)] at hm
          linarith
        · rw [abs_of_pos (sub_pos.mpr hgt)] at hm
          linarith
      have hzs : z∉sphere (0:Euclidean n) ρ := by simpa only [mem_sphere,dist_zero_right] using hz
      rw [indicator_of_notMem hzs]
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with m hm
      exact (indicator_of_notMem hm _).symm
  have hi := tendsto_integral_of_dominated_convergence
    (μ := (Q : Measure (Euclidean n))) (fun _ => (1:ℝ))
    (fun m => ((measurable_const.indicator (hAm m)).aestronglyMeasurable))
    (integrable_const 1) (fun m => Eventually.of_forall fun z => by
      by_cases hz : z∈A m <;> simp [hz]) (Eventually.of_forall hlim)
  simp only [integral_indicator (hAm _),integral_indicator isClosed_sphere.measurableSet,
    setIntegral_const,smul_eq_mul,mul_one,Measure.real,hnull,ENNReal.toReal_zero] at hi
  intro η hη
  obtain ⟨m,hm⟩ := (hi.eventually (Iio_mem_nhds (half_pos hη))).exists
  refine ⟨q m,hqpos m,hqlt m,?_⟩
  have hf : Tendsto (fun k => (ν k).toFiniteMeasure) atTop (𝓝 Q.toFiniteMeasure) :=
    (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto Q).comp hν
  have ht := finite_measure_closed_eventual_bound (A := A m) hf
    (isClosed_closedBall.sdiff isOpen_ball) (half_pos hη)
  filter_upwards [ht] with k hk
  change (ν k : Measure (Euclidean n)).real (A m) ≤
    (Q : Measure (Euclidean n)).real (A m)+η/2 at hk
  change (Q : Measure (Euclidean n)).real (A m) < η/2 at hm
  change (ν k : Measure (Euclidean n)).real (A m) < η
  linarith

end RegularPointCoordinates

end

end OAI
