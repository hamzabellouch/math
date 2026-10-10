import OAI.MathematicalPhysics.NavierStokes.Material.Machines
import OAI.MathematicalPhysics.NavierStokes.Material.Decoder
import OAI.MathematicalPhysics.NavierStokes.Material.Signal

namespace OAI

namespace Alternating.Memory

def alphabetBase (M : Machine) : ℕ := 2 * (1 + max (M.stateCount + 1) M.symbolCount)

theorem alphabetBase_ge_four (M : Machine) : 4 ≤ alphabetBase M := by
  have h := Nat.le_max_left (M.stateCount + 1) M.symbolCount
  dsimp [alphabetBase, Machine.stateCount] at *
  omega

theorem state_digit_allowed {M : Machine} {q : ℕ} (hq : q ≤ M.stateCount) :
    Even (2 * q) ∧ 2 * q + 2 ≤ alphabetBase M := by
  refine ⟨even_two_mul q, ?_⟩
  have h := Nat.le_max_left (M.stateCount + 1) M.symbolCount
  dsimp [alphabetBase]
  omega

theorem symbol_digit_allowed {M : Machine} {a : ℕ} (ha : a < M.symbolCount) :
    Even (2 * a) ∧ 2 * a + 2 ≤ alphabetBase M := by
  refine ⟨even_two_mul a, ?_⟩
  have h := Nat.le_max_right (M.stateCount + 1) M.symbolCount
  dsimp [alphabetBase]
  omega

def leftDigits (K : ℕ) (c : Configuration) : List ℕ :=
  (List.range K).map (fun i : ℕ => 2 * c.tape (c.head - 1 - (i : ℤ)))

def rightDigits (K : ℕ) (c : Configuration) : List ℕ :=
  (List.range K).map (fun i : ℕ => 2 * c.tape (c.head + (i : ℤ)))

theorem leftDigits_allowed {M : Machine} {c : Configuration} (hc : c.ValidFor M) (K : ℕ) :
    AllowedDigits (alphabetBase M) (leftDigits K c) := by
  intro d hd
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hd
  exact symbol_digit_allowed (hc.2 _)

theorem rightDigits_allowed {M : Machine} {c : Configuration} (hc : c.ValidFor M) (K : ℕ) :
    AllowedDigits (alphabetBase M) (rightDigits K c) := by
  intro d hd
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hd
  exact symbol_digit_allowed (hc.2 _)

def actualBlock (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    Block (alphabetBase I.1) (width I.2.length n) where
  stateDigit := 2 * (configurationAt I n).state
  left := leftDigits (width I.2.length n) (configurationAt I n)
  right := rightDigits (width I.2.length n) (configurationAt I n)
  state_allowed := state_digit_allowed (configurationAt_valid hI n).1
  left_allowed := leftDigits_allowed (configurationAt_valid hI n) _
  right_allowed := rightDigits_allowed (configurationAt_valid hI n) _
  left_length := by simp [leftDigits]
  right_length := by simp [rightDigits]

theorem actualBlock_full_tape (I : MachineInput) (n : ℕ) {i : ℕ} (hi : width I.2.length n ≤ i) :
    (configurationAt I n).tape ((configurationAt I n).head - 1 - (i : ℤ)) = 0 ∧
    (configurationAt I n).tape ((configurationAt I n).head + (i : ℤ)) = 0 := by
  have hhead := configurationAt_head_bounds I n
  dsimp [width] at hi
  constructor
  · apply configurationAt_tape_outside I n
    left
    omega
  · apply configurationAt_tape_outside I n
    right
    omega

theorem actualBlock_left_get (I : MachineInput) (hI : ValidInput I) (n i : ℕ)
    (hi : i < width I.2.length n) :
    (actualBlock I hI n).left[i]'(by simpa [actualBlock, leftDigits] using hi) =
      2 * (configurationAt I n).tape ((configurationAt I n).head - 1 - (i : ℤ)) := by
  simp only [actualBlock, leftDigits, List.getElem_map, List.getElem_range]

theorem actualBlock_right_get (I : MachineInput) (hI : ValidInput I) (n i : ℕ)
    (hi : i < width I.2.length n) :
    (actualBlock I hI n).right[i]'(by simpa [actualBlock, rightDigits] using hi) =
      2 * (configurationAt I n).tape ((configurationAt I n).head + (i : ℤ)) := by
  simp only [actualBlock, rightDigits, List.getElem_map, List.getElem_range]

theorem actualBlock_read (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    let b := alphabetBase I.1
    let N := I.2.length
    let D := donor b N (actualBlock I hI) n
    safeDecoder b ((b : ℝ) ^ scale N n * D) = (actualBlock I hI n).code ∧
    safeDecoder b ((b : ℝ) ^ (scale N n + 1 + width N n) * D) = (actualBlock I hI n).rightCode ∧
    safeDecoder b ((b : ℝ) ^ (scale N n + 1) * D) -
      (b : ℝ)⁻¹ ^ width N n * safeDecoder b ((b : ℝ) ^ (scale N n + 1 + width N n) * D) =
      (actualBlock I hI n).leftCode := by
  exact safe_read_exact (by have := alphabetBase_ge_four I.1; omega) (actualBlock I hI) n

theorem actualSignal_hit_iff (I : MachineInput) :
    (∃ (n : ℕ) (u : ℝ), u ∈ Set.Icc 0 1 ∧
      0 < signalAlong (alphabetBase I.1) I.2.length
        (fun j => I.1.isHalting (configurationAt I j).state) n u) ↔ Halts I := by
  exact signal_hit_iff (by have := alphabetBase_ge_four I.1; omega) I.2.length _

end Alternating.Memory

end OAI
