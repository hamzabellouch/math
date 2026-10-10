import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.CappedTransform

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction

theorem scalarCappedTransform_memLp_bound_of_bilinear {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f : Ambient d →ᵇ ℝ) (B : ℝ≥0)
    (hB : ∀ g : Ambient d →ᵇ ℝ,
      |∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q ∂μ.prod μ| ≤
        (B : ℝ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (∫ x, f x ^ 2 ∂μ)) :
    MemLp (scalarCappedTransform m μ e ε f) 2 μ ∧
      eLpNorm (scalarCappedTransform m μ e ε f) 2 μ ≤ (B : ℝ≥0∞) * eLpNorm f 2 μ := by
  have hf : MemLp f 2 μ :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖ (Eventually.of_forall f.norm_coe_le_norm)
  have hf1 := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  obtain ⟨T, hT⟩ := exists_boundedContinuous_scalarCappedTransform m μ e ε hε
    f f.continuous.measurable hf1
  have hTm : MemLp T 2 μ :=
    MemLp.of_bound T.continuous.aestronglyMeasurable ‖T‖ (Eventually.of_forall T.norm_coe_le_norm)
  have heq : scalarCappedTransform m μ e ε f = T := funext fun x => (hT x).symm
  rw [heq]
  have hpair : (∫ q : Ambient d × Ambient d, T q.1 * f q.2 * scalarCappedRieszKernel m e ε q
      ∂μ.prod μ) = ∫ x, T x ^ 2 ∂μ := by
    rw [capped_bilinear_eq_scalarCappedTransform m μ e ε hε f T
      f.continuous.measurable T.continuous.measurable hf1 (hTm.integrable (by norm_num)), heq]
    simp only [pow_two]
  have hI0 : 0 ≤ ∫ x, T x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (T x)
  have hb := hB T
  rw [hpair, abs_of_nonneg hI0] at hb
  have hsqrt : Real.sqrt (∫ x, T x ^ 2 ∂μ) ≤ (B : ℝ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
    by_cases hz : Real.sqrt (∫ x, T x ^ 2 ∂μ) = 0
    · rw [hz]
      positivity
    have hp : 0 < Real.sqrt (∫ x, T x ^ 2 ∂μ) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    by_contra hn
    have hpos := mul_pos
      (sub_pos.mpr (lt_of_not_ge hn)) hp
    nlinarith [Real.sq_sqrt hI0]
  have hnorm : ‖hTm.toLp T‖ ≤ (B : ℝ) * ‖hf.toLp f‖ := by
    simpa only [toLp_norm_eq_sqrt_integral] using! hsqrt
  refine ⟨hTm, ?_⟩
  have he := ENNReal.ofReal_le_ofReal hnorm
  simpa only [Lp.norm_toLp, ENNReal.ofReal_mul B.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_toReal hTm.eLpNorm_ne_top, ENNReal.ofReal_toReal hf.eLpNorm_ne_top] using! he

end

end RieszRectifiability

end OAI
