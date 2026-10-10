import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma weak_probability_open_le_limsup {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs atTop (𝓝 μ)) (G : Set X) (hG : IsOpen G) :
    (μ : Measure X).real G ≤ limsup (fun n => (μs n : Measure X).real G) atTop := by
  have hh := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hG
  have he : liminf (fun n => (μs n : Measure X).real G) atTop =
      (liminf (fun n => (μs n : Measure X) G) atTop).toReal :=
    ENNReal.liminf_toReal_eq (by norm_num : (1:ℝ≥0∞) ≠ ∞)
      (Eventually.of_forall fun n => (prob_le_one : (μs n : Measure X) G ≤ 1))
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => (μs n : Measure X).real G) :=
    isBoundedUnder_of ⟨1,fun n => measureReal_le_one⟩
  have hc : IsBoundedUnder (· ≥ ·) atTop (fun n => (μs n : Measure X).real G) :=
    isBoundedUnder_of ⟨0,fun n => measureReal_nonneg⟩
  have hfin : (liminf (fun n => (μs n : Measure X) G) atTop) ≠ ∞ := by
    apply ne_top_of_le_ne_top (by norm_num : (1:ℝ≥0∞)≠∞)
    exact (liminf_le_limsup).trans (limsup_le_of_le (h := Eventually.of_forall fun n => (prob_le_one : (μs n : Measure X) G ≤ 1)))
  have hi : (μ : Measure X).real G ≤ liminf (fun n => (μs n : Measure X).real G) atTop := by
    rw [he]
    exact ENNReal.toReal_mono hfin hh
  exact hi.trans (liminf_le_limsup hb hc)

lemma weak_probability_limsup_closed_le {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs atTop (𝓝 μ)) (G : Set X) (hG : IsClosed G) :
    limsup (fun n => (μs n : Measure X).real G) atTop ≤ (μ : Measure X).real G := by
  have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hG
  change limsup (fun n => ((μs n : Measure X) G).toReal) atTop ≤ _
  rw [ENNReal.limsup_toReal_eq (f := atTop) (by norm_num : (1:ℝ≥0∞)≠∞)
    (Eventually.of_forall fun n => (prob_le_one : (μs n : Measure X) G ≤ 1))]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hh

lemma weak_tail_comparison
    (μs νs : ℕ → ProbabilityMeasure unitInterval) (μ ν : ProbabilityMeasure unitInterval)
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (ht : ∀ u > 0, u < 1 →
      limsup (fun n => (μs n : Measure unitInterval).real {x | u < (x:ℝ)}) atTop ≤
      C * limsup (fun n => (νs n : Measure unitInterval).real {y | u/D < (y:ℝ)}) atTop) :
    ∀ u > 0, (μ : Measure unitInterval) {x | u < (x:ℝ)} ≤
      ENNReal.ofReal C * (ν : Measure unitInterval) {y | u/(2*D) < (y:ℝ)} := by
  intro u hu
  by_cases hu1 : u < 1
  · have hop : IsOpen {x : unitInterval | u < (x:ℝ)} := isOpen_lt continuous_const continuous_subtype_val
    have hcl : IsClosed {x : unitInterval | u/D ≤ (x:ℝ)} := isClosed_le continuous_const continuous_subtype_val
    have hsub : ∀ n, (νs n : Measure unitInterval).real {y | u/D < (y:ℝ)} ≤
        (νs n : Measure unitInterval).real {y | u/D ≤ (y:ℝ)} :=
      fun n => measureReal_mono (by intro y hy; exact (show u/D < (y:ℝ) from hy).le) (measure_ne_top _ _)
    have hs := limsup_le_limsup (Eventually.of_forall hsub)
      (isBoundedUnder_of (r := (· ≥ ·)) ⟨0,fun n => measureReal_nonneg⟩).isCoboundedUnder_le
      (show IsBoundedUnder (· ≤ ·) atTop (fun n => (νs n : Measure unitInterval).real {y | u/D ≤ (y:ℝ)}) from
        isBoundedUnder_of ⟨1,fun n => measureReal_le_one⟩)
    have hre : (μ : Measure unitInterval).real {x | u < (x:ℝ)} ≤
        C * (ν : Measure unitInterval).real {y | u/(2*D) < (y:ℝ)} := by
      refine (weak_probability_open_le_limsup μs μ hμ _ hop).trans ((ht u hu hu1).trans ?_)
      apply mul_le_mul_of_nonneg_left _ hC
      refine hs.trans ((weak_probability_limsup_closed_le νs ν hν _ hcl).trans ?_)
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro y hy
      have hh : u/(2*D) < u/D := by
        apply (div_lt_div_iff₀ (by positivity) hD).mpr
        nlinarith
      exact hh.trans_le hy
    have hh := ENNReal.ofReal_le_ofReal hre
    simpa only [ENNReal.ofReal_mul hC,ofReal_measureReal (measure_ne_top _ _)] using hh
  · have he : {x : unitInterval | u < (x:ℝ)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_lt.mpr (x.2.2.trans (le_of_not_gt hu1))) hx
    rw [he,measure_empty]
    exact bot_le

end DirectionalTransience

end

end

end OAI
