import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourceMetadataProgram

namespace OAI

/-! Convert the runtime bound of an actual unary-output procedure into a
single fixed power of the source input length, as needed by calibration. -/

namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram

theorem natPolynomial_power_bound (p : Polynomial ℕ) :
    ∃ k : ℕ, ∀ n : ℕ, p.eval n ≤ (n + 2) ^ k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b + 1, fun n => ?_⟩
    have hbase : 1 ≤ n + 2 := by omega
    have hpa : (n + 2) ^ a ≤ (n + 2) ^ (a + b) :=
      pow_le_pow_right₀ hbase (by omega)
    have hpb : (n + 2) ^ b ≤ (n + 2) ^ (a + b) :=
      pow_le_pow_right₀ hbase (by omega)
    rw [Polynomial.eval_add, pow_succ]
    calc
      p.eval n + q.eval n ≤ (n + 2) ^ (a + b) + (n + 2) ^ (a + b) :=
        Nat.add_le_add ((ha n).trans hpa) ((hb n).trans hpb)
      _ = (n + 2) ^ (a + b) * 2 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  | monomial i c =>
    refine ⟨c + i, fun n => ?_⟩
    have hc : c ≤ (n + 2) ^ c :=
      (Nat.lt_two_pow_self (n := c)).le.trans (Nat.pow_le_pow_left (by omega) c)
    rw [Polynomial.eval_monomial, pow_add]
    exact Nat.mul_le_mul hc (Nat.pow_le_pow_left (by omega) i)

theorem unaryProcedure_power_bound {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea unaryCode f) :
    ∃ k : ℕ, ∀ a, f a ≤ ((ea a).length + 2) ^ k := by
  obtain ⟨k, hk⟩ := natPolynomial_power_bound (Polynomial.X + p.bound)
  refine ⟨k, fun a => ?_⟩
  have h := p.output_length_le a
  simp only [unaryCode, List.length_replicate] at h
  exact h.trans (by simpa only [Polynomial.eval_add, Polynomial.eval_X] using hk (ea a).length)

end ContinuumCoulomb

end OAI
