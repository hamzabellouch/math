import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.PartitionEnergy

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

theorem cellMean_mul_mass (μ : Measure X) (w : X → ℝ) (hμ : μ.real univ ≠ 0) :
    μ.real univ * cellMean μ w = ∫ x, w x ∂μ := by
  unfold cellMean
  field_simp

theorem cellMean_sq_mass_le (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (hμ : μ.real univ ≠ 0) :
    μ.real univ * (cellMean μ w) ^ 2 ≤ ∫ x, w x ^ 2 ∂μ := by
  have hv := integral_sq_sub_const μ w hw (cellMean μ w)
  rw [← cellMean_mul_mass μ w hμ] at hv
  have hpos : 0 ≤ ∫ x, (w x - cellMean μ w) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  nlinarith

theorem cellMean_abs_bound (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ)
    (c B : ℝ) (hc : 0 < c) (hmass : c ≤ μ.real univ)
    (hB : (∫ x, w x ^ 2 ∂μ) ≤ B) :
    |cellMean μ w| ≤ B / c + 1 := by
  have hμ : 0 < μ.real univ := lt_of_lt_of_le hc hmass
  have hs : (cellMean μ w) ^ 2 ≤ B / c := by
    apply (le_div_iff₀ hc).2
    calc
      _ = c * (cellMean μ w) ^ 2 := mul_comm _ _
      _ ≤ μ.real univ * (cellMean μ w) ^ 2 :=
        mul_le_mul_of_nonneg_right hmass (sq_nonneg _)
      _ ≤ _ := (cellMean_sq_mass_le μ w hw hμ.ne').trans hB
  have hsmall : |cellMean μ w| ≤ (cellMean μ w) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|cellMean μ w| - 1), sq_abs (cellMean μ w), sq_nonneg (cellMean μ w)]
  linarith

end

end RieszRectifiability

end OAI
