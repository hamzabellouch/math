import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.MultiplicityRestriction
import OAI.Geometry.CAT0Fillings.Currents.ActionSeries
import OAI.Geometry.CAT0Fillings.Prism.Family
import OAI.Geometry.CAT0Fillings.Prism.IntegralAction

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory Measure Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] {k : ℕ}
noncomputable def timeAction {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]
    (hT : IsMetricCurrent T) (v : Fin (k+1) → ℝ × X → ℝ) (t : ℝ) : ℝ :=
  ∑ i, (-1:ℝ)^i.val * BorelCoefficients.borelAction μ hT
    (fun x => deriv (fun s => v i (s,x)) t) (fun j x => v (i.succAbove j) (t,x))

lemma timeAction_bound {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]
    (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (v : Fin (k+1) → ℝ × X → ℝ) (K : ℝ≥0) (hv : ∀ i, LipschitzWith K (v i)) (t : ℝ) :
    |timeAction μ hT v t| ≤ ((k+1:ℝ)*(K:ℝ)^(k+1))*μ.real univ := by
  have hi (i : Fin (k+1)) : |BorelCoefficients.borelAction μ hT
      (fun x => deriv (fun s => v i (s,x)) t) (fun j x => v (i.succAbove j) (t,x))| ≤
      (K:ℝ)^(k+1)*μ.real univ := by
    have hb := BorelCoefficients.borelAction_bound μ hT hμ
      (integrable_timeDeriv (hv i) μ t) (fun j x => v (i.succAbove j) (t,x)) (fun _ => K)
      (fun j => lipschitz_slice (hv _) t)
    have hI : (∫ x, |deriv (fun s => v i (s,x)) t| ∂μ) ≤ μ.real univ*(K:ℝ) := by
      have H := integral_mono (integrable_timeDeriv (hv i) μ t).abs
        (integrable_const (K:ℝ)) (fun x => norm_deriv_le_of_lipschitz (lipschitz_time (hv i) x))
      simpa only [integral_const,smul_eq_mul] using H
    calc
      _ ≤ (K:ℝ)^k * ∫ x, |deriv (fun s => v i (s,x)) t| ∂μ := by simpa using hb
      _ ≤ (K:ℝ)^k*(μ.real univ*(K:ℝ)) := mul_le_mul_of_nonneg_left hI (pow_nonneg K.coe_nonneg _)
      _ = _ := by rw [pow_succ]; ring
  calc
    _ ≤ ∑ i : Fin (k+1), |(-1:ℝ)^i.val * BorelCoefficients.borelAction μ hT
      (fun x => deriv (fun s => v i (s,x)) t) (fun j x => v (i.succAbove j) (t,x))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (k+1), (K:ℝ)^(k+1)*μ.real univ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using hi i
    _ = _ := by simp; ring

lemma IntegerChart.integrable_timeAction [Nonempty X] (C : IntegerChart X k)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls C.action μ)
    (v : Fin (k+1) → ℝ × X → ℝ) (K : ℝ≥0) (hv : ∀ i, LipschitzWith K (v i)) :
    Integrable (timeAction μ C.action_isMetricCurrent v) (volume.restrict (Icc (0:ℝ) 1)) := by
  apply integrable_finsetSum
  intro i _
  apply Integrable.const_mul
  have hi := (C.integrable_prism_minor_derivative v K hv i).integral_prod_left
  convert hi using 1
  funext t
  apply C.borelAction_eq_integral C.action_isMetricCurrent hμ
    ((measurable_timeDeriv (hv i).continuous).comp (measurable_const.prodMk measurable_id))
    ⟨K,fun x => norm_deriv_le_of_lipschitz (lipschitz_time (hv i) x)⟩
    _ (fun j => ⟨K,lipschitz_slice (hv _) t⟩)

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Measure Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

lemma prismFamily_action_one {T : Functional X k} (hT : IsMetricCurrent T)
    (C : ℕ → IntegerChart X k) (hs : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π)
    (v : Fin (k+1) → ℝ × X → ℝ) (K : ℝ≥0) (hv : ∀ i, LipschitzWith K (v i)) :
    ∃ (μ : Measure X) (_ : IsFiniteMeasure μ), Controls T μ ∧
      prismFamily C (fun _ => 1) v = ∫ t in (0:ℝ)..1, timeAction μ hT v t := by
  choose μ hfin hμ he using fun j => (C j).action_isMetricCurrent.exists_controls_mass_eq
  let : ∀ j, IsFiniteMeasure (μ j) := hfin
  have hsμ : Summable (fun j => (μ j).real univ) := by simpa only [←he] using hs
  let : IsFiniteMeasure (Measure.sum μ) := finite_sum_measure_of_summable_total μ hsμ
  refine ⟨Measure.sum μ,inferInstance,controls_sum_general hμ heq,?_⟩
  let F (j : ℕ) (t : ℝ) := timeAction (μ j) (C j).action_isMetricCurrent v t
  have hFi (j) : Integrable (F j) (volume.restrict (Icc (0:ℝ) 1)) :=
    (C j).integrable_timeAction (μ j) (hμ j) v K hv
  have hsF : Summable (fun j => ∫ t, ‖F j t‖ ∂volume.restrict (Icc (0:ℝ) 1)) := by
    apply (hsμ.mul_left ((k+1:ℝ)*(K:ℝ)^(k+1))).of_nonneg_of_le
      (fun j => integral_nonneg (fun _ => norm_nonneg _))
    intro j
    have H := integral_mono (hFi j).norm
      (integrable_const (((k+1:ℝ)*(K:ℝ)^(k+1))*(μ j).real univ))
      (fun t => timeAction_bound (μ j) (C j).action_isMetricCurrent (hμ j) v K hv t)
    simpa [measureReal_def] using H
  have hsum (t) : (∑' j, F j t) = timeAction (Measure.sum μ) hT v t := by
    have hS (i : Fin (k+1)) : Summable (fun j =>
        BorelCoefficients.borelAction (μ j) (C j).action_isMetricCurrent
          (fun x => deriv (fun s => v i (s,x)) t) (fun l x => v (i.succAbove l) (t,x))) :=
      BorelCoefficients.summable_borelAction μ (fun j => (C j).action_isMetricCurrent) hμ
        (integrable_timeDeriv (hv i) (Measure.sum μ) t) _
        (fun l => ⟨K,lipschitz_slice (hv _) t⟩)
    dsimp only [F,timeAction]
    rw [Summable.tsum_finsetSum (fun i _ => (hS i).mul_left _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [tsum_mul_left]
    congr 1
    exact (BorelCoefficients.borelAction_sum μ hT
      (fun j => (C j).action_isMetricCurrent) hμ heq
        (integrable_timeDeriv (hv i) (Measure.sum μ) t) _
        (fun l => ⟨K,lipschitz_slice (hv _) t⟩)).symm
  calc
    _ = ∑' j, ∫ t, F j t ∂volume.restrict (Icc (0:ℝ) 1) := by
      apply tsum_congr
      intro j
      rw [(C j).prism_action_one_eq_integral (μ j) (hμ j) v K hv,
        intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),←integral_Icc_eq_integral_Ioc]
      rfl
    _ = ∫ t, ∑' j, F j t ∂volume.restrict (Icc (0:ℝ) 1) :=
      (hasSum_integral_of_summable_integral_norm hFi hsF).tsum_eq
    _ = _ := by
      simp only [hsum]
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),←integral_Icc_eq_integral_Ioc]

end CAT0Fillings
end
end

end OAI
