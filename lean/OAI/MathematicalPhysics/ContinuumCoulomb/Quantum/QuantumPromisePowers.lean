import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLatticeEnvelope

namespace OAI

/-! Small power bounds for the unary tuples used by the actual coefficient
programs. The exponent is independent of the particular verifier. -/

namespace ContinuumCoulomb.QuantumCoefficientPrograms
open ExactQuantumFactoring.BitStackProgram

private theorem tuple_power (n k : ℕ) :
    16*(n+2)^k ≤ (n+2)^(k+4) := by
  have h : 16 ≤ (n+2)^4 := by
    simpa using (Nat.pow_le_pow_left (show 2 ≤ n+2 by omega) 4)
  rw [pow_add]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left ((n+2)^k) h

theorem inputCode_power {n k m L T : ℕ}
    (hm : m ≤ (n+2)^k) (hL : L ≤ (n+2)^k) (hT : T ≤ (n+2)^k) :
    (inputCode (m,L,T)).length+2 ≤ (n+2)^(k+4) := by
  have hp : 1 ≤ (n+2)^k := Nat.one_le_pow k (n+2) (by omega)
  calc
    _ ≤ 16*(n+2)^k := by
      simp only [inputCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
      omega
    _ ≤ _ := tuple_power n k

theorem latticeInputCode_power {n k m r L T : ℕ}
    (hm : m ≤ (n+2)^k) (hr : r ≤ (n+2)^k)
    (hL : L ≤ (n+2)^k) (hT : T ≤ (n+2)^k) :
    (latticeInputCode (m,r,L,T)).length+2 ≤ (n+2)^(k+4) := by
  have hp : 1 ≤ (n+2)^k := Nat.one_le_pow k (n+2) (by omega)
  calc
    _ ≤ 16*(n+2)^k := by
      simp only [latticeInputCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
      omega
    _ ≤ _ := tuple_power n k

theorem input_function_power {f : Input → ℕ} {a : ℕ}
    (hf : ∀ x, f x ≤ ((inputCode x).length+2)^a)
    {n k m L T : ℕ} (hm : m ≤ (n+2)^k)
    (hL : L ≤ (n+2)^k) (hT : T ≤ (n+2)^k) :
    f (m,L,T) ≤ (n+2)^((k+4)*a) := by
  calc
    _ ≤ ((inputCode (m,L,T)).length+2)^a := hf _
    _ ≤ ((n+2)^(k+4))^a := Nat.pow_le_pow_left (inputCode_power hm hL hT) a
    _ = _ := (pow_mul _ _ _).symm

theorem lattice_function_power {f : LatticeInput → ℕ} {a : ℕ}
    (hf : ∀ x, f x ≤ ((latticeInputCode x).length+2)^a)
    {n k m r L T : ℕ} (hm : m ≤ (n+2)^k) (hr : r ≤ (n+2)^k)
    (hL : L ≤ (n+2)^k) (hT : T ≤ (n+2)^k) :
    f (m,r,L,T) ≤ (n+2)^((k+4)*a) := by
  calc
    _ ≤ ((latticeInputCode (m,r,L,T)).length+2)^a := hf _
    _ ≤ ((n+2)^(k+4))^a := Nat.pow_le_pow_left (latticeInputCode_power hm hr hL hT) a
    _ = _ := (pow_mul _ _ _).symm

theorem power_base_change {n k : ℕ} (hn : 0 < n) : (n+2)^k ≤ (n+1)^(2*k) := by
  have h : n+2 ≤ (n+1)^2 := by nlinarith
  calc
    _ ≤ ((n+1)^2)^k := Nat.pow_le_pow_left h k
    _ = _ := (pow_mul _ _ _).symm

end ContinuumCoulomb.QuantumCoefficientPrograms

end OAI
