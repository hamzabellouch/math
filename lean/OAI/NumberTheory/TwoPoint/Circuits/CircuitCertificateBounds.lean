import OAI.NumberTheory.TwoPoint.Circuits.CircuitCertifiedGate
import OAI.NumberTheory.TwoPoint.Circuits.CircuitSampleNorm
import OAI.NumberTheory.TwoPoint.Circuits.CircuitApproximationDegree

namespace OAI

/-! Numerical bounds carried by the recursive polynomial/error-circuit
construction. They retain explicit circuit dependence until the final
size and depth estimates. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace AC0Circuit

noncomputable def sampleNormBound {n : ℕ} (s : ℕ) : AC0Circuit n → ℝ
  | .literal _ _ => 1
  | .andGate (k := k) c =>
    1 + (1 + (k : ℝ) * (2 + ∑ i, sampleNormBound s (c i))) ^ (s * (Nat.log 2 k + 3))
  | .orGate (k := k) c =>
    1 + (1 + (k : ℝ) * (2 + ∑ i, sampleNormBound s (c i))) ^ (s * (Nat.log 2 k + 3))

def exceptionSizeBound {n : ℕ} (s : ℕ) : AC0Circuit n → ℕ
  | .literal _ _ => 1
  | .andGate (k := k) c =>
    4 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
      (1 + k * (1 + ∑ i, (c i).size)) + ∑ i, exceptionSizeBound s (c i)
  | .orGate (k := k) c =>
    4 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
      (1 + k * (1 + ∑ i, (c i).size)) + ∑ i, exceptionSizeBound s (c i)

lemma sampleNormBound_nonneg {n : ℕ} (s : ℕ) (c : AC0Circuit n) :
    0 ≤ c.sampleNormBound s := by
  induction c with
  | literal i b => exact zero_le_one
  | andGate c ih | orGate c ih =>
    have hh : 0 ≤ ∑ i, (c i).sampleNormBound s := sum_nonneg (fun i _ => ih i)
    simp only [sampleNormBound]
    positivity

lemma negate_indicator {n : ℕ} (c : AC0Circuit n) (x : BooleanCube n) :
    c.negate.indicator x = 1 - c.indicator x := by
  have he : c.negate.eval x = !(c.eval x) := by
    apply Bool.eq_iff_iff.mpr
    rw [negate_eval]
    simp
  simp only [indicator, he]
  cases c.eval x <;> norm_num

end AC0Circuit

structure CircuitCertificate {n : ℕ} (ν : FiniteLaw (BooleanCube n))
    (s : ℕ) (c : AC0Circuit n) where
  polynomial : BooleanCube n → ℝ
  error : AC0Circuit n
  degree_bound : WalshDegreeLE polynomial (c.approximationDegree s)
  error_depth : error.depth ≤ 4 * c.depth + 1
  error_size : error.size ≤ c.exceptionSizeBound s
  error_probability : ν.probability (fun x => error.eval x = true) ≤
    (c.size : ℝ) * (7 / 8 : ℝ) ^ s
  exact_off_error : ∀ x, error.eval x ≠ true → polynomial x = c.indicator x
  norm_bound : ∀ x, |polynomial x| ≤ c.sampleNormBound s

noncomputable def CircuitCertificate.literal {n : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (s : ℕ) (i : Fin n) (b : Bool) :
    CircuitCertificate ν s (.literal i b) where
  polynomial := (AC0Circuit.literal i b).indicator
  error := AC0Circuit.falseCircuit n
  degree_bound := literal_indicator_degree i b
  error_depth := by simp [AC0Circuit.falseCircuit, AC0Circuit.depth]
  error_size := by simp [AC0Circuit.falseCircuit, AC0Circuit.size, AC0Circuit.exceptionSizeBound]
  error_probability := by
    simp only [AC0Circuit.falseCircuit_eval, Bool.false_eq_true, FiniteLaw.probability,
      ite_false, FiniteLaw.average_const]
    positivity
  exact_off_error := fun _ _ => rfl
  norm_bound := by
    intro x
    unfold AC0Circuit.indicator
    split_ifs <;> norm_num [AC0Circuit.sampleNormBound]

end TwoPointCorrelations

end OAI
