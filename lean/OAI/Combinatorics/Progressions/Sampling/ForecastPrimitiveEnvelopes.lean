import OAI.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_forecast_primitive_envelopes (L : ℝ≥0) :
    ∃ pcap : ℝ, 1 ≤ pcap ∧
      scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ pcap ∧
      pcap ≤ Real.exp pcap ∧
      ∀ (T : ℕ) (_hT : 0 < T) (v : ℝ), 0 ≤ v → (T : ℝ) ≤ Real.exp v →
        1 ≤ pcap * T ∧ 0 ≤ pcap + v ∧
        pcap * T ≤ Real.exp (pcap + v) ∧
        scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ pcap * T := by
  let pcap := max 1 (scalarCubePrimitiveEnvelope Empty L 1 0 1)
  have hpcap : 1 ≤ pcap := le_max_left _ _
  have hcap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ pcap := le_max_right _ _
  have hexp : pcap ≤ Real.exp pcap := by linarith [Real.add_one_le_exp pcap]
  refine ⟨pcap, hpcap, hcap, hexp, ?_⟩
  intro T hT v hv hTv
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  refine ⟨one_le_mul_of_one_le_of_one_le hpcap hT1,
    add_nonneg (zero_le_one.trans hpcap) hv, ?_, ?_⟩
  · rw [Real.exp_add]
    exact mul_le_mul hexp hTv (Nat.cast_nonneg _) (Real.exp_nonneg _)
  · have hscaled := scalarCubePrimitiveEnvelope_le_scaled Empty L 1 0 hT
    simp only [Fintype.card_empty, zero_add, pow_one] at hscaled
    exact hscaled.trans (mul_le_mul_of_nonneg_right hcap (Nat.cast_nonneg _))

end Erdos3

end

end OAI
