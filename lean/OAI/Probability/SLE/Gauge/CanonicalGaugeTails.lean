import OAI.Probability.SLE.Gauge.CanonicalDiskMomentTails
import OAI.Probability.SLE.Gauge.GaugeTailSum

namespace OAI

/-! All prescribed gauge entries have a summable limiting centered-disk tail,
including repeated dyadic entries and the cleanup sequence. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)
  (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
  (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
  (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)

include C hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW

lemma limitingDiskTail_all_batches_bound :
    (∑' e : Target.GaugeIndex κ W, C.limitingDiskTail hc (16*Target.weights κ W e)) ≤
      ENNReal.ofReal (Target.moment κ W 1/16) + ENNReal.ofReal (2/3:ℝ) := by
  rw [Target.gauge_tail_sum_eq]
  apply add_le_add (C.limitingDiskTail_cleanup_bound hB hc h0 hκ hκ8 F hw hgrowth W hW)
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (2*(1/4:ℝ)^(n+1)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      exact (C.limitingDiskTail_batch_bound hB hc h0 hκ hκ8 F hw hgrowth W hW
        (by omega) (C.moment_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW (n+1))).trans
        (ENNReal.ofReal_le_ofReal (MomentBatches.upper_constant_le_geometric (by omega)))
    _ = ENNReal.ofReal (2/3:ℝ) := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
        ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/4)]
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric_add_one]
      rw [← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ)≤1/4),
        ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<1-1/4),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/4),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
      norm_num

theorem limitingDiskTail_summable :
    (∑' e : Target.GaugeIndex κ W, C.limitingDiskTail hc (16*Target.weights κ W e)) ≠ ∞ := by
  exact ne_top_of_le_ne_top (by finiteness)
    (C.limitingDiskTail_all_batches_bound hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW)

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
