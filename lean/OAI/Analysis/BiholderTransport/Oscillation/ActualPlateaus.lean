import Mathlib
import OAI.Analysis.BiholderTransport.Oscillation.SectionOscillation

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction
open Filter

section ActualPlateaus
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in

lemma exists_actual_plateau_section {vol : Measure M} {lam cap : ℝ} {x0 : M}
    (hc : (densityDualClass vol lam cap x0).Nonempty)
    (hno : ¬ HasPowerUpperBound (classOscillation vol lam cap x0))
    {J : ℝ} (hJ : 1 ≤ J) :
    ∃ A : ℝ, ∃ uv ∈ densityDualClass vol lam cap x0, ∃ x y0 y1 : M,
      J ^ 2 ≤ A ∧
      y0 ∈ gapSection uv.1 uv.2 x (Real.exp (-(A + J))) ∧
      y1 ∈ gapSection uv.1 uv.2 x (Real.exp (-(A + J))) ∧
      (∀ y ∈ gapSection uv.1 uv.2 x (Real.exp (-(A + J))), uv.2 y0 ≤ uv.2 y) ∧
      (∀ y ∈ gapSection uv.1 uv.2 x (Real.exp (-(A + J))), uv.2 y ≤ uv.2 y1) ∧
      sectionOscillation uv.1 uv.2 x (Real.exp (-(A + J))) = uv.2 y1 - uv.2 y0 ∧
      0 < uv.2 y1 - uv.2 y0 ∧
      classOscillation vol lam cap x0 (Real.exp (-A)) ≤
        Real.exp (2 / J) * (uv.2 y1 - uv.2 y0) ∧
      |Real.log (uv.2 y1 - uv.2 y0)| ≤
        |Real.log (1 + Metric.diam (univ : Set M) ^ 2)| + A / J ^ 2 + J⁻¹ := by
  let F := classOscillation vol lam cap x0
  let CF : ℝ := 1 + Metric.diam (univ : Set M) ^ 2
  have hCF : 0 < CF := by dsimp [CF]; positivity
  have hJ0 : 0 < J := zero_lt_one.trans_le hJ
  have hJi : 0 < J⁻¹ := inv_pos.mpr hJ0
  have hmono : MonotoneOn F (Ioi 0) :=
    (classOscillation_monotone hc).mono Ioi_subset_Ici_self
  have hbound : ∀ r : ℝ, 0 < r → F r ≤ CF := by
    intro r hr
    exact (classOscillation_bounds hc hr.le).2.trans (by dsimp [CF]; linarith)
  obtain ⟨A, hA, hplateau, hlog⟩ := no_power_gap_scale_plateau hCF hbound hmono hno hJ
  have hp : 0 < F (Real.exp (-(A + J))) := positive_of_no_power hmono hno (Real.exp_pos _)
  have hq : Real.exp (-J⁻¹) * F (Real.exp (-(A + J))) < F (Real.exp (-(A + J))) := by
    have hh := mul_lt_mul_of_pos_right (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hJi)) hp
    simpa only [one_mul] using hh
  obtain ⟨uv, huv, x, y0, y1, hy0, hy1, hmin, hmax, heq, hlarge⟩ :=
    exists_section_with_large_oscillation hc (Real.exp_pos _).le hq
  have hDpos : 0 < uv.2 y1 - uv.2 y0 := (mul_pos (Real.exp_pos _) hp).trans hlarge
  have hDle : uv.2 y1 - uv.2 y0 ≤ F (Real.exp (-(A + J))) := by
    rw [← heq]
    exact sectionOscillation_le_classOscillation huv x (Real.exp_pos _).le
  refine ⟨A, uv, huv, x, y0, y1, hA, hy0, hy1, hmin, hmax, heq, hDpos, ?_, ?_⟩
  · have hFle : F (Real.exp (-(A + J))) ≤ Real.exp J⁻¹ * (uv.2 y1 - uv.2 y0) := by
      calc
        F (Real.exp (-(A + J))) =
            Real.exp J⁻¹ * (Real.exp (-J⁻¹) * F (Real.exp (-(A + J)))) := by
          rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp J⁻¹ * (uv.2 y1 - uv.2 y0) :=
          mul_le_mul_of_nonneg_left hlarge.le (Real.exp_pos _).le
    calc
      F (Real.exp (-A)) ≤ Real.exp J⁻¹ * F (Real.exp (-(A + J))) := hplateau
      _ ≤ Real.exp J⁻¹ * (Real.exp J⁻¹ * (uv.2 y1 - uv.2 y0)) :=
        mul_le_mul_of_nonneg_left hFle (Real.exp_pos _).le
      _ = Real.exp (2 / J) * (uv.2 y1 - uv.2 y0) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  · have hupper := Real.log_le_log hDpos hDle
    have hlower := Real.log_lt_log (mul_pos (Real.exp_pos _) hp) hlarge
    rw [Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp] at hlower
    apply abs_le.mpr
    constructor
    · have hh := neg_le_abs (Real.log (F (Real.exp (-(A + J)))))
      linarith
    · have hh := le_abs_self (Real.log (F (Real.exp (-(A + J)))))
      linarith

end ActualPlateaus

end WeakMTWTransport

end
end
end

end OAI
