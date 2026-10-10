import OAI.Analysis.CircleDomains.Uniformization.SquareAverageLimit
import OAI.Analysis.CircleDomains.Sobolev.AverageSquareBound
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! Coarse square averages are small when the global L2 mass is small. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma abs_unitSquareAverage_le_half {f : ℝ × ℝ → ℝ} (hf : MemLp f 2 volume)
    (hsmall : (∫ p, f p^2) ≤ 1) (c : ℝ × ℝ) :
    |squareAverage f c 1| ≤ 1/2 := by
  let μ := volume.restrict (coordinateSquare c 1)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (coordinateSquare_compact c 1).measure_lt_top.ne
  let : NeZero μ := ⟨by
    simpa [μ] using coordinateSquare_volume_ne_zero c (by norm_num)⟩
  have hfm : MemLp f 2 μ := hf.mono_measure Measure.restrict_le_self
  have hJ := sq_average_le_average_sq (hfm.integrable (by norm_num)) hfm.integrable_sq
  have hglobal : (∫ p, f p^2 ∂μ) ≤ 1 :=
    (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun p => sq_nonneg (f p))
      hf.integrable_sq).trans hsmall
  have hm : μ.real univ = 4 := by
    change (volume.restrict (coordinateSquare c 1)).real univ = 4
    rw [measureReal_restrict_apply_univ, coordinateSquare_real_volume c (by norm_num)]
    norm_num
  have havg2 : (⨍ p, f p^2 ∂μ) = (4:ℝ)⁻¹*(∫ p, f p^2 ∂μ) := by
    rw [average_eq, hm, smul_eq_mul]
  rw [havg2] at hJ
  change (squareAverage f c 1)^2 ≤ _ at hJ
  nlinarith [sq_abs (squareAverage f c 1), abs_nonneg (squareAverage f c 1)]

end CircleDomainRigidity

end

end OAI
