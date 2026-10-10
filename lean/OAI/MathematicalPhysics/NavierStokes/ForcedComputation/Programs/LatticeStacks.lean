import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LatticeMachine

namespace OAI

/-! Finite little-endian stack codes and the effective support bound for the
actual machine's marked tape. The width grows twice as fast as the head. -/

namespace ForcedComputation.Lattice

def stackValue (b : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | d + 1, a => a 0 + b * stackValue b d (fun i => a (i + 1))

theorem stackValue_ext (b d : ℕ) {a c : ℕ → ℕ}
    (h : ∀ i < d, a i = c i) : stackValue b d a = stackValue b d c := by
  induction d generalizing a c with
  | zero => rfl
  | succ d ih =>
      simp only [stackValue]
      rw [h 0 (by omega), ih (fun i hi => h (i + 1) (by omega))]

theorem stackValue_zero (b d : ℕ) : stackValue b d (fun _ => 0) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [stackValue, ih, Nat.mul_zero, Nat.zero_add]

theorem stackValue_lt {b : ℕ} (_hb : 0 < b) (d : ℕ) {a : ℕ → ℕ}
    (ha : ∀ i < d, a i < b) : stackValue b d a < b ^ d := by
  induction d generalizing a with
  | zero => simp only [stackValue, pow_zero]; omega
  | succ d ih =>
      have ht := ih (a := fun i => a (i + 1)) (fun i hi => ha (i + 1) (by omega))
      simpa only [stackValue, pow_succ, Nat.mul_comm] using prepend_lt (ha 0 (by omega)) ht

theorem stackValue_head {b d : ℕ} {a : ℕ → ℕ} (ha : a 0 < b) :
    stackValue b (d + 1) a % b = a 0 := by
  simp only [stackValue, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem stackValue_tail {b d : ℕ} (hb : 0 < b) {a : ℕ → ℕ} (ha : a 0 < b) :
    stackValue b (d + 1) a / b = stackValue b d (fun i => a (i + 1)) := by
  rw [stackValue, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha, Nat.zero_add]

theorem stackValue_add (b d e : ℕ) (a : ℕ → ℕ) :
    stackValue b (d + e) a = stackValue b d a + b ^ d * stackValue b e (fun i => a (d + i)) := by
  induction d generalizing a with
  | zero => simp only [Nat.zero_add, stackValue, pow_zero, Nat.one_mul]
  | succ d ih =>
      rw [Nat.succ_add, stackValue, ih, stackValue, pow_succ]
      have he : (fun i => a (d + i + 1)) = (fun i => a (d + 1 + i)) := by
        funext i
        congr 1
        omega
      rw [he]
      ring

theorem stackValue_extend (b d e : ℕ) (a : ℕ → ℕ)
    (hz : ∀ i, d ≤ i → a i = 0) : stackValue b (d + e) a = stackValue b d a := by
  rw [stackValue_add]
  have he : stackValue b e (fun i => a (d + i)) = 0 := by
    rw [stackValue_ext b e (a := fun i => a (d + i)) (c := fun _ => 0)
      (fun i _ => hz _ (by omega)), stackValue_zero]
  rw [he, Nat.mul_zero, Nat.add_zero]

def configurationWidth (I : Alternating.MachineInput) (n : ℕ) : ℕ := I.2.length + 1 + 2 * n

def leftDigits (C : Alternating.Configuration) (i : ℕ) : ℕ :=
  markedTape C (C.head - 1 - (i : ℤ))

def rightDigits (C : Alternating.Configuration) (i : ℕ) : ℕ :=
  markedTape C (C.head + (i : ℤ))

theorem configurationWidth_pos (I : Alternating.MachineInput) (n : ℕ) :
    0 < configurationWidth I n := by unfold configurationWidth; omega

theorem configurationWidth_succ (I : Alternating.MachineInput) (n : ℕ) :
    configurationWidth I (n + 1) = configurationWidth I n + 2 := by
  unfold configurationWidth
  omega

theorem marked_tape_outside (I : Alternating.MachineInput) (n : ℕ) {j : ℤ}
    (hj : j < -(n : ℤ) ∨ (I.2.length : ℤ) + n ≤ j) (hzero : j ≠ 0) :
    markedTape (Alternating.configurationAt I n) j = 0 := by
  rw [markedTape, Alternating.configurationAt_tape_outside I n hj]
  simp [markedDigit, hzero]

theorem leftDigits_zero (I : Alternating.MachineInput) (n i : ℕ)
    (hi : configurationWidth I n ≤ i) : leftDigits (Alternating.configurationAt I n) i = 0 := by
  have hh := Alternating.configurationAt_head_bounds I n
  unfold configurationWidth at hi
  apply marked_tape_outside I n
  · left
    omega
  · omega

theorem rightDigits_zero (I : Alternating.MachineInput) (n i : ℕ)
    (hi : configurationWidth I n ≤ i) : rightDigits (Alternating.configurationAt I n) i = 0 := by
  have hh := Alternating.configurationAt_head_bounds I n
  unfold configurationWidth at hi
  apply marked_tape_outside I n
  · right
    omega
  · omega

def configurationCode (I : Alternating.MachineInput) (n : ℕ) : ℕ :=
  let C := Alternating.configurationAt I n
  let d := configurationWidth I n
  pack (machineBase I.1) d
    (stackValue (machineBase I.1) d (leftDigits C))
    (stackValue (machineBase I.1) d (rightDigits C)) C.state

theorem configurationCode_lt (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (n : ℕ) : configurationCode I n < period (machineBase I.1) (configurationWidth I n) := by
  have hv := Alternating.configurationAt_valid hI n
  have hb : 0 < machineBase I.1 := lt_of_lt_of_le (by decide) (machineBase_two_le I.1)
  apply pack_lt
  · apply stackValue_lt hb
    intro i _
    exact markedTape_lt hv _
  · apply stackValue_lt hb
    intro i _
    exact markedTape_lt hv _
  · have h := machineBase_states I.1
    have hstate := hv.1
    omega

end ForcedComputation.Lattice

end OAI
