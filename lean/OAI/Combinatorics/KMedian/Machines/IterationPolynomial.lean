import Mathlib
import OAI.Combinatorics.KMedian.Machines.Iteration

namespace OAI

section Inline_PCPIterationPolynomial

namespace MetricKMedian.PCP
open scoped Classical BigOperators

namespace Amplifier
lemma log_power_bound (c e : ℕ) (he : 0<e) : c^(Nat.log 2 e) ≤ e^c := by
  calc
    _ ≤ (2^c)^(Nat.log 2 e) := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
    _ = (2^(Nat.log 2 e))^c := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
    _ ≤ e^c := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (Nat.ne_of_gt he)) _
namespace Box
variable (C : Box)
lemma amplified_edges_polynomial : C.amplified.edges ≤ edgeCoefficient*(C.edges^edgeCoefficient*C.edges) := by
  calc
    _ ≤ edgeCoefficient^C.count*C.edges := C.iterate_edges _
    _ = edgeCoefficient*(edgeCoefficient^(Nat.log 2 C.edges)*C.edges) := by
      rw [count,pow_succ']; exact Nat.mul_assoc _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (log_power_bound _ _ C.edges_pos))
lemma amplified_size_polynomial : C.amplified.nodes+C.amplified.edges ≤
    sizeCoefficient*(C.edges^edgeCoefficient*C.edges) := by
  calc
    _ ≤ sizeCoefficient*edgeCoefficient^(Nat.log 2 C.edges)*C.edges := C.iterate_size _
    _ ≤ sizeCoefficient*(C.edges^edgeCoefficient*C.edges) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (log_power_bound _ _ C.edges_pos))
end Box
end Amplifier
end MetricKMedian.PCP

end Inline_PCPIterationPolynomial

end OAI
