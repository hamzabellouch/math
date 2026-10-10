import OAI.Probability.SpanningForest.FactorAssembly
import OAI.Probability.SpanningForest.SlopeReadout

namespace OAI

noncomputable section
open Filter

namespace Problem336.FactorAssembly

theorem rule_eq_slopeReadout (b : GraphDrift) (w : GraphNoise)
    (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) :
    rule b w G U e =
      SlopeReadout.readout (fun n => Picard.decode (w G U) (b G) e (n : ℝ)) := by
  classical
  have hs := Filter.limsup_nat_add (decodedSlope b w G U e) 1
  unfold rule SlopeReadout.readout SlopeReadout.slope
  rw [← hs]
  rfl

theorem rule_eq_readout_family (b : GraphDrift) (w : GraphNoise)
    (G : GraphCode) (U : ℕ → ℝ) :
    rule b w G U = SlopeReadout.family
      (fun e n => Picard.decode (w G U) (b G) e (n : ℝ)) := by
  funext e
  exact rule_eq_slopeReadout b w G U e

end Problem336.FactorAssembly

end

end OAI
