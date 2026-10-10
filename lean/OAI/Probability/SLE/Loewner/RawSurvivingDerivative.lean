import OAI.Probability.SLE.Angle.TargetFlowEvolution
import OAI.Probability.SLE.Loewner.TargetSurvivalExtension

namespace OAI

/-! The raw flow has its ordinary right evolution at every surviving
time, because the strict cutoff certificate persists a little longer. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

lemma flow_hasDerivWithinAt_of_survival (b : Driver) (z : ℂ) {T : ℝ}
    (hT : 0 ≤ T) (hs : Surviving 1 b z T) :
    HasDerivWithinAt (flow 1 b z)
      (2/(flow 1 b z T-(b T.toNNReal:ℂ))) (Ici 0) T := by
  obtain ⟨S,hTS,hS⟩ := exists_later_survival 1 b z hT hs
  simpa only [a,div_one,Complex.ofReal_ofNat,driverValue] using
    flow_hasDerivWithinAt_of_later_survival 1 b z T S hT hTS hS

end SLEExactGauge.Target

end

end OAI
