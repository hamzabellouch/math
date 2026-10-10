import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalHeightPairingContinuity
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalTruncatedSpatialDecay

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology

theorem height_fractional_truncated_integral_tendsto (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (f : Ambient (p + 1) → ℝ) (hf : Measurable f)
    (hweight : Integrable (fun x => |f x| * polynomialDecay (p + 3) x) μ)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (g : 𝓢(Ambient (p + 1), ℂ)) (hg : (∫ y, g y) = 0) :
    Tendsto (fun j => ∫ x, f x • fractionalSchwartzTruncatedTest p (ε j) g x ∂μ)
      atTop (𝓝 (∫ x, f x • fractionalSchwartzTest p g x ∂μ)) := by
  let W := 3 ^ (p + 3) * (fractionalSchwartzUniformSize p g + fractionalSchwartzDecaySize p g)
  have hm (j : ℕ) : Measurable (fun x => f x • fractionalSchwartzTruncatedTest p (ε j) g x) := by
    simp_rw [RCLike.real_smul_eq_coe_mul]
    exact (Complex.continuous_ofReal.measurable.comp hf).mul
      (fractionalSchwartzTruncatedTest_measurable p (ε j) g)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => W * (|f x| * polynomialDecay (p + 3) x))
  · exact Eventually.of_forall fun j => (hm j).aestronglyMeasurable
  · filter_upwards [hε.eventually (gt_mem_nhds zero_lt_one)] with j hj
    exact Eventually.of_forall fun x => by
      rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
      calc
        _ ≤ |f x| * (W * polynomialDecay (p + 3) x) :=
          mul_le_mul_of_nonneg_left
            (fractionalSchwartzTruncatedTest_polynomial_decay p (ε j) hj.le g hg x) (abs_nonneg _)
        _ = _ := by ring
  · exact hweight.const_mul W
  · exact Eventually.of_forall fun x =>
      (fractionalSchwartzTruncatedTest_tendsto p ε hε g x).const_smul (f x)

end

end RieszRectifiability

end OAI
