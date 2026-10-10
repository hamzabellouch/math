import OAI.Analysis.PlanarPacking.TableEnvelopes
import OAI.Analysis.PlanarPacking.CoefficientClose

namespace OAI

namespace SharpPlanar
lemma exact_table_error (a : Bool) (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    |exactJet a ell t-tableHJet a ell t| ≤ 
      (3:ℝ)/10^5*(directEnvelope ell+transformEnvelope ell s) := by
  rw [abs_sub_comm]
  apply (jet_error_bound a ell (hs.trans hst)).trans
  change ‖coefficientError a‖*directEnvelope ell+
    ‖coefficientError (!a)‖*transformEnvelope ell t ≤ _
  have h1:=mul_le_mul_of_nonneg_right (coefficient_error_bound a).le (directEnvelope_nonneg ell)
  have h2:=mul_le_mul (coefficient_error_bound (!a)).le (transformEnvelope_antitone ell hs hst)
    (transformEnvelope_nonneg ell (hs.trans hst)) (by norm_num : (0:ℝ) ≤ 3/10^5)
  nlinarith
end SharpPlanar

end OAI
