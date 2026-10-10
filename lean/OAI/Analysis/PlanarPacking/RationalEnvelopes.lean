import OAI.Analysis.PlanarPacking.RationalBounds
import OAI.Analysis.PlanarPacking.TableEnvelopes

namespace OAI

namespace SharpPlanar
lemma table_jet_rat (a : Bool) (ell n : ℕ) {s : ℝ} (hs : (n:ℝ) ≤ s) :
    |tableHJet a ell s| ≤ taylorEnvelope ell n := by
  apply (table_jet_envelope a ell (Nat.cast_nonneg n) hs).trans
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le pi_le_upper ell) (by norm_num))
    (mul_le_mul_of_nonneg_left (transformEnvelope_le_rat ell n) (by norm_num)))
    (mul_le_mul_of_nonneg_left (atomicEnvelope_le_rat ell n) (by norm_num))
end SharpPlanar

end OAI
