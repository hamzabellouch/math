import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CappedEnergyContinuity
import OAI.Analysis.RieszRectifiability.Kernel.LipschitzL2Density

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal

theorem capped_energy_bound_from_lipschitz_tests {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (v : Ambient d → ℝ) (hv : MemLp v 2 μ)
    (E : ℝ) (hE : 0 ≤ E)
    (htests : ∀ (g : Ambient d → ℝ) (K B : ℝ≥0), LipschitzWith K g →
      (∀ x, |g x| ≤ (B : ℝ)) → MemLp g 2 μ →
      (∫ q : Ambient d × Ambient d, (v q.1 - v q.2) * cappedTestKernel m ε g q ∂μ.prod μ) ^ 2 ≤
        E * ∫ q, cappedPairEnergy m ε g q ∂μ.prod μ) :
    (∫ q, cappedPairEnergy m ε v q ∂μ.prod μ) ≤ E := by
  obtain ⟨g, K, B, _, hLip, hbound, hg, herror⟩ := exists_bounded_lipschitz_L2_sequence μ v hv
  have hpair := capped_pairing_tendsto_of_L2_error m ε hε μ g v hg hv herror
  have henergy := capped_energy_tendsto_of_L2_error m ε hε μ g v hg hv herror
  have hlim : (∫ q, cappedPairEnergy m ε v q ∂μ.prod μ) ^ 2 ≤
      E * ∫ q, cappedPairEnergy m ε v q ∂μ.prod μ :=
    le_of_tendsto_of_tendsto (hpair.pow 2) (henergy.const_mul E)
      (Filter.Eventually.of_forall fun k => htests (g k) (K k) (B k) (hLip k) (hbound k) (hg k))
  by_contra h
  have hgt : E < ∫ q, cappedPairEnergy m ε v q ∂μ.prod μ := lt_of_not_ge h
  have hpos := hE.trans_lt hgt
  nlinarith [mul_pos hpos (sub_pos.mpr hgt)]

end

end RieszRectifiability

end OAI
