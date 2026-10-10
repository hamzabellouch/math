import OAI.Geometry.RCD.Metric.MetricLimitConstantDensity

namespace OAI

/-! # Recovering the measure from its constant interior density -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem restrict_eq_volume_of_constant_density {n : ℕ} (μ : Measure (Euclidean n))
    [IsFiniteMeasure μ] {U : Set (Euclidean n)} (hU : MeasurableSet U)
    (hac : μ.restrict U ≪ volume) {c : ℝ}
    (hc : ∀ᵐ x ∂volume.restrict U, ((μ.restrict U).rnDeriv volume x).toReal=c) :
    μ.restrict U = ENNReal.ofReal c • volume.restrict U := by
  have he : (μ.restrict U).rnDeriv volume =ᵐ[volume.restrict U]
      fun _ => ENNReal.ofReal c := by
    filter_upwards [hc, ae_restrict_of_ae (Measure.rnDeriv_ne_top (μ.restrict U) volume)] with x hx hfin
    rw [← hx, ENNReal.ofReal_toReal hfin]
  calc
    μ.restrict U = (μ.restrict U).restrict U := by rw [Measure.restrict_restrict hU, inter_self]
    _ = (volume.withDensity ((μ.restrict U).rnDeriv volume)).restrict U := by
      rw [Measure.withDensity_rnDeriv_eq _ _ hac]
    _ = (volume.restrict U).withDensity ((μ.restrict U).rnDeriv volume) :=
      restrict_withDensity hU _
    _ = (volume.restrict U).withDensity (fun _ => ENNReal.ofReal c) :=
      withDensity_congr_ae he
    _ = ENNReal.ofReal c • volume.restrict U := withDensity_const _

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_limit_measure {K : ℝ} {n : ℕ}
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
    ∃ c : ℝ, 0 < c ∧ (Q : Measure (Euclidean n)).restrict (ball 0 S) =
      ENNReal.ofReal c • volume.restrict (ball 0 S) := by
  obtain ⟨c,hc0,hc⟩ := hX.metric_limit_constant_density hn hK hS p r ε V hr hε hcurv
    hVm hV hfin hlim hpositive
  have he := restrict_eq_volume_of_constant_density (Q : Measure (Euclidean n))
    measurableSet_ball (hX.metric_limit_absolutelyContinuous hn hK hS p r ε V hr hε hcurv
      hVm hV hfin hlim hpositive) hc
  refine ⟨c,lt_of_le_of_ne hc0 ?_,he⟩
  intro hc
  have hz : c=0 := hc.symm
  have hmass := hpositive 0 (mem_ball_self hS) S hS
  have hm := congrArg (fun ν : Measure (Euclidean n) => ν.real (ball 0 S)) he
  simp [hz,Measure.real,Measure.restrict_apply measurableSet_ball,inter_self] at hm
  exact hmass.ne' hm

end RegularPointCoordinates

end

end OAI
