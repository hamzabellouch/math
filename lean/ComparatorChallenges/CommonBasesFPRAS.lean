import Mathlib

namespace OAI

namespace CommonBasesFPRAS

abbrev IndependenceOracle (n : ℕ) := Bool → (Fin n → Bool) → Bool

def ExactOracles {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (O : IndependenceOracle n) : Prop :=
  ∀ (which : Bool) (A : Fin n → Bool),
    O which A = true ↔ (if which then M₂ else M₁).Indep {i | A i = true}

noncomputable def commonBaseCount {n : ℕ} (M₁ M₂ : Matroid (Fin n)) : ℕ :=
  Nat.card {A : Finset (Fin n) // M₁.IsBase (A : Set (Fin n)) ∧
    M₂.IsBase (A : Set (Fin n))}

inductive Instruction (k s : ℕ) where
  | push (register : Fin (k + 8)) (bit : Bool) (next : Fin (s + 1))
  | pop (register : Fin (k + 8)) (empty zero one : Fin (s + 1))
  | coin (zero one : Fin (s + 1))
  | query (which : Bool) (register : Fin (k + 8)) (no yes : Fin (s + 1))
  | halt

def Program (k s : ℕ) := Fin (s + 1) → Instruction k s

def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * binaryValue l

structure MachineConfig (k s : ℕ) where
  registers : Fin (k + 8) → List Bool
  control : Fin (s + 1)
  output : Option ℚ := none
  oracleCalls : ℕ := 0
  bitOperations : ℕ := 0

def inputLength (n r : ℕ) (ε δ : ℚ) : ℕ :=
  6 + n.bits.length + r.bits.length + ε.num.natAbs.bits.length + ε.den.bits.length +
    δ.num.natAbs.bits.length + δ.den.bits.length

def initialConfig (k s n r : ℕ) (ε δ : ℚ) : MachineConfig k s where
  registers := fun i => match i.val with
    | 0 => n.bits
    | 1 => r.bits
    | 2 => ε.num.natAbs.bits
    | 3 => ε.den.bits
    | 4 => δ.num.natAbs.bits
    | 5 => δ.den.bits
    | _ => []
  control := 0

def machineStep {k s n : ℕ} (P : Program k s) (O : IndependenceOracle n)
    (randomBit : Bool) (c : MachineConfig k s) : MachineConfig k s :=
  if c.output.isSome then c else
  match P c.control with
  | .push i b next =>
    { c with
      registers := Function.update c.registers i (b :: c.registers i)
      control := next
      bitOperations := c.bitOperations + 1 }
  | .pop i empty zero one =>
    match c.registers i with
    | [] => { c with
      control := empty
      bitOperations := c.bitOperations + 1 }
    | b :: l =>
      { c with
      registers := Function.update c.registers i l
      control := if b then one else zero
      bitOperations := c.bitOperations + 1 }
  | .coin zero one =>
    { c with
      control := if randomBit then one else zero
      bitOperations := c.bitOperations + 1 }
  | .query which i no yes =>
    if (c.registers i).length = n then
      { c with
      control := if O which (fun j => (c.registers i)[j.val]?.getD false)
          then yes else no
      oracleCalls := c.oracleCalls + 1
      bitOperations := c.bitOperations + (c.registers i).length + n + 1 }
    else
      { c with
      output := some 0
      bitOperations := c.bitOperations + (c.registers i).length + n + 1 }
  | .halt =>
    { c with
      output := some ((binaryValue (c.registers ⟨6, by omega⟩) : ℚ) /
        (binaryValue (c.registers ⟨7, by omega⟩) : ℚ))
      bitOperations := c.bitOperations + (c.registers ⟨6, by omega⟩).length +
        (c.registers ⟨7, by omega⟩).length + 1 }

def execution {k s n : ℕ} (P : Program k s) (O : IndependenceOracle n)
    (c : MachineConfig k s) (bits : ℕ → Bool) : ℕ → MachineConfig k s
  | 0 => c
  | t + 1 => machineStep P O (bits t) (execution P O c bits t)

def finiteBits {B : ℕ} (bits : Fin B → Bool) (t : ℕ) : Bool :=
  if h : t < B then bits ⟨t, h⟩ else false

def relativeAccuracy (ε : ℚ) (Z : ℕ) (z : ℚ) : Prop :=
  (1-ε)*(Z:ℚ)≤z ∧ z≤(1+ε)*(Z:ℚ)

def resourceBound (C d n r : ℕ) (ε δ : ℚ) : ℕ :=
  C * (1 + n + inputLength n r ε δ + ⌈ε⁻¹⌉₊ + Nat.clog 2 ⌈δ⁻¹⌉₊) ^ d

def MainTheorem : Prop :=
  ∃ (k s : ℕ) (P : Program k s) (C d : ℕ), 0 < C ∧
    ∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
      (ε δ : ℚ),
      M₁.E = Set.univ → M₂.E = Set.univ →
      M₁.eRank = (r : ℕ∞) → M₂.eRank = (r : ℕ∞) →
      ExactOracles M₁ M₂ O → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      let B := resourceBound C d n r ε δ
      let Z := commonBaseCount M₁ M₂
      (∀ bits : ℕ → Bool,
        let out := execution P O (initialConfig k s n r ε δ) bits B
        out.output.isSome ∧ out.oracleCalls ≤ B ∧ out.bitOperations ≤ B ∧
        ∀ z, out.output = some z → 0 ≤ z ∧ (Z = 0 → z = 0)) ∧
      (1 - δ) * (2 : ℚ) ^ B ≤
        (Nat.card {bits : Fin B → Bool //
          ∃ z, (execution P O (initialConfig k s n r ε δ) (finiteBits bits) B).output
            = some z ∧ relativeAccuracy ε Z z} : ℚ)

end CommonBasesFPRAS

theorem common_bases_fpras : CommonBasesFPRAS.MainTheorem := by
  sorry

end OAI
