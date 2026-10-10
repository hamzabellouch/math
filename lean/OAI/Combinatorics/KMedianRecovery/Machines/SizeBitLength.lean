import Mathlib
import OAI.Combinatorics.KMedianRecovery.Model

namespace OAI

namespace MetricKMedianRecovery.RationalMetricInput

theorem size_le_bitLength (I : RationalMetricInput) : I.size ≤ I.bits.length := by
  have hc : I.clients.card ≤ I.pointCount := by
    simpa using (Finset.card_le_univ I.clients)
  have hf : I.facilities.card ≤ I.pointCount := by
    simpa using (Finset.card_le_univ I.facilities)
  have hm : 2*I.pointCount ≤ I.bits.length := by
    simp only [bits,List.length_append,List.length_ofFn]
    omega
  unfold size
  omega

theorem polynomial_size_bound (I : RationalMetricInput) (C d : ℕ) :
    C*I.size^d+C ≤ C*I.bits.length^d+C := by
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left I.size_le_bitLength d)) C

end MetricKMedianRecovery.RationalMetricInput

end OAI
