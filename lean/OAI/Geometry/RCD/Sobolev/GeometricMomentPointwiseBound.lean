import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Geometric bounds for integer moments give a pointwise density bound -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

theorem continuous_le_of_geometric_moments {f : X → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) {M B : ℝ} (hB : 0 < B)
    (hi : ∀ j : ℕ, Integrable (fun x => (f x)^(j+2)) μ)
    (hm : ∀ j : ℕ, (∫ x, (f x)^(j+2) ∂μ) ≤ M*B^(j+2)) :
    ∀ x, f x ≤ B := by
  intro x
  by_contra hx
  have hxf : B < f x := lt_of_not_ge hx
  let a := (B+f x)/2
  have hBa : B < a := by dsimp only [a]; linarith
  have haf : a < f x := by dsimp only [a]; linarith
  have ha : 0 < a := hB.trans hBa
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    (hf.continuousAt.preimage_mem_nhds (Ioi_mem_nhds haf))
  have hfin : μ (ball x r) < ∞ := (measure_mono ball_subset_closedBall).trans_lt
    (isCompact_closedBall x r).measure_lt_top
  have hv : 0 < μ.real (ball x r) := ENNReal.toReal_pos (measure_ball_pos μ x hr).ne' hfin.ne
  have hpow (j : ℕ) : a^(j+2)*μ.real (ball x r) ≤ M*B^(j+2) := by
    calc
      _ = ∫ y in ball x r, a^(j+2) ∂μ := by simp [mul_comm]
      _ ≤ ∫ y in ball x r, (f y)^(j+2) ∂μ := by
        apply integral_mono_ae (integrableOn_const (C := a^(j+2)) hfin.ne) (hi j).integrableOn
        filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        exact pow_le_pow_left₀ ha.le (le_of_lt (hball hy)) _
      _ ≤ ∫ y, (f y)^(j+2) ∂μ :=
        setIntegral_le_integral (hi j) (Eventually.of_forall fun y => pow_nonneg (hf0 y) _)
      _ ≤ _ := hm j
  have hbound (j : ℕ) : μ.real (ball x r) ≤ M*(B/a)^(j+2) := by
    have hh : μ.real (ball x r) ≤ M*B^(j+2)/a^(j+2) :=
      (le_div_iff₀ (pow_pos ha _)).mpr (by simpa only [mul_comm] using hpow j)
    simpa only [div_pow,mul_div_assoc] using hh
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hB.le ha.le)
    ((div_lt_one ha).mpr hBa)
  have hlim' : Tendsto (fun j : ℕ => M*(B/a)^(j+2)) atTop (𝓝 0) := by
    simpa only [pow_add,mul_zero,zero_mul] using (hlim.mul_const ((B/a)^2)).const_mul M
  have hz : μ.real (ball x r) ≤ 0 := ge_of_tendsto hlim' (Eventually.of_forall hbound)
  exact (not_le_of_gt hv) hz

end RegularPointCoordinates

end

end OAI
