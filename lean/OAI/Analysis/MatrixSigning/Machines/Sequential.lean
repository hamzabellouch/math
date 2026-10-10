import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FiniteDispatch

namespace OAI

section

namespace KS.W29
namespace Sequential

def leftState (M N : BinaryMachine) (s : Fin M.states) : Fin (M.states + N.states) :=
  ⟨s.val, by have h := s.isLt; omega⟩

def rightState (M N : BinaryMachine) (s : Fin N.states) : Fin (M.states + N.states) :=
  ⟨M.states + s.val, by have h := s.isLt; omega⟩

def liftLeft (M N : BinaryMachine) (c : Config M.states) : Config (M.states + N.states) :=
  ⟨some (match c.state with
      | none => rightState M N N.initial
      | some s => leftState M N s), c.«stacks»⟩

def liftRight (M N : BinaryMachine) (c : Config N.states) : Config (M.states + N.states) :=
  ⟨c.state.map (rightState M N), c.«stacks»⟩

def leftInstruction (M N : BinaryMachine) (i : Instruction M.states) :
    Instruction (M.states + N.states) :=
  ⟨some (match i.next with
      | none => rightState M N N.initial
      | some s => leftState M N s), i.first, i.second, i.third⟩

def rightInstruction (M N : BinaryMachine) (i : Instruction N.states) :
    Instruction (M.states + N.states) :=
  ⟨i.next.map (rightState M N), i.first, i.second, i.third⟩

def fetch (M : BinaryMachine) (s : Fin M.states) (heads : Fin 27) (b : Bool) :
    Instruction M.states :=
  M.table.getD (54 * s.val + 2 * heads.val + bitCode b) (Instruction.halt M.states)

def dispatch (M N : BinaryMachine) (s : Fin (M.states + N.states))
    (heads : Fin 27) (b : Bool) : Instruction (M.states + N.states) :=
  if h : s.val < M.states then
    leftInstruction M N (fetch M ⟨s.val, h⟩ heads b)
  else
    rightInstruction M N
      (fetch N ⟨s.val - M.states, by have hs := s.isLt; omega⟩ heads b)

def compose (M N : BinaryMachine) : BinaryMachine :=
  FiniteDispatch.compile (leftState M N M.initial) (dispatch M N)

theorem dispatch_left (M N : BinaryMachine) (s : Fin M.states) (heads : Fin 27) (b : Bool) :
    dispatch M N (leftState M N s) heads b = leftInstruction M N (fetch M s heads b) := by
  simp [dispatch, leftState, s.isLt]

theorem dispatch_right (M N : BinaryMachine) (s : Fin N.states) (heads : Fin 27) (b : Bool) :
    dispatch M N (rightState M N s) heads b = rightInstruction M N (fetch N s heads b) := by
  simp [dispatch, rightState]

theorem step_left (M N : BinaryMachine) (s : Fin M.states) («stacks» : Fin 3 → List Bool)
    (b : Bool) :
    (compose M N).step ⟨some (leftState M N s), «stacks»⟩ b =
      liftLeft M N (M.step ⟨some s, «stacks»⟩ b) := by
  unfold compose
  rw [FiniteDispatch.step_compile]
  dsimp only
  rw [dispatch_left]
  rfl

theorem step_right (M N : BinaryMachine) (s : Fin N.states) («stacks» : Fin 3 → List Bool)
    (b : Bool) :
    (compose M N).step ⟨some (rightState M N s), «stacks»⟩ b =
      liftRight M N (N.step ⟨some s, «stacks»⟩ b) := by
  unfold compose
  rw [FiniteDispatch.step_compile]
  dsimp only
  rw [dispatch_right]
  rfl

theorem step_liftRight (M N : BinaryMachine) (c : Config N.states) (b : Bool) :
    (compose M N).step (liftRight M N c) b = liftRight M N (N.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s => exact step_right M N s «stacks» b

theorem run_liftRight (M N : BinaryMachine) (c : Config N.states) (bits : List Bool) :
    (compose M N).run (liftRight M N c) bits = liftRight M N (N.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (compose M N).run ((compose M N).step (liftRight M N c) b) bs =
        liftRight M N (N.run (N.step c b) bs)
      erw [step_liftRight M N c b]
      exact ih (N.step c b)

def ActiveFor (M : BinaryMachine) : Config M.states → List Bool → Prop
  | _, [] => True
  | c, b :: bs => c.state ≠ none ∧ ActiveFor M (M.step c b) bs

def HaltsAfter (M : BinaryMachine) (c : Config M.states) (bits : List Bool) : Prop :=
  ActiveFor M c bits ∧ (M.run c bits).state = none

theorem step_liftLeft (M N : BinaryMachine) (c : Config M.states) (b : Bool)
    (h : c.state ≠ none) :
    (compose M N).step (liftLeft M N c) b = liftLeft M N (M.step c b) := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => exact (h rfl).elim
  | some s => exact step_left M N s «stacks» b

theorem run_liftLeft (M N : BinaryMachine) (c : Config M.states) (bits : List Bool)
    (h : ActiveFor M c bits) :
    (compose M N).run (liftLeft M N c) bits = liftLeft M N (M.run c bits) := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      change (compose M N).run ((compose M N).step (liftLeft M N c) b) bs =
        liftLeft M N (M.run (M.step c b) bs)
      erw [step_liftLeft M N c b h.1]
      exact ih _ h.2

theorem run_compose (M N : BinaryMachine) (c : Config M.states) (first second : List Bool)
    (h : HaltsAfter M c first) :
    (compose M N).run (liftLeft M N c) (first ++ second) =
      liftRight M N (N.run ⟨some N.initial, (M.run c first).«stacks»⟩ second) := by
  erw [BinaryMachine.run_append, run_liftLeft M N c first h.1]
  have he : liftLeft M N (M.run c first) =
      liftRight M N ⟨some N.initial, (M.run c first).«stacks»⟩ := by
    simp [liftLeft, liftRight, h.2]
  rw [he, run_liftRight]

theorem exists_halting_prefix (M : BinaryMachine) (c : Config M.states) (bits : List Bool)
    (h : (M.run c bits).state = none) :
    ∃ first rest, bits = first ++ rest ∧ HaltsAfter M c first := by
  induction bits generalizing c with
  | nil => exact ⟨[], [], rfl, ⟨trivial, h⟩⟩
  | cons b bs ih =>
      by_cases hc : c.state = none
      · exact ⟨[], b :: bs, rfl, ⟨trivial, hc⟩⟩
      · obtain ⟨first, rest, heq, ha⟩ := ih (M.step c b) h
        refine ⟨b :: first, rest, ?_, ?_⟩
        · simp [heq]
        · exact ⟨⟨hc, ha.1⟩, ha.2⟩

theorem compose_halts (M N : BinaryMachine) (c : Config M.states)
    (first second : List Bool) (hfirst : HaltsAfter M c first)
    (hsecond : (N.run ⟨some N.initial, (M.run c first).«stacks»⟩ second).state = none) :
    ((compose M N).run (liftLeft M N c) (first ++ second)).state = none := by
  rw [run_compose M N c first second hfirst]
  simp [liftRight, hsecond]
  rfl

def HaltsFromWithin (M : BinaryMachine) (c : Config M.states) (fuel : Nat) : Prop :=
  ∀ bits : List Bool, bits.length = fuel → (M.run c bits).state = none

theorem haltsFromWithin_mono (M : BinaryMachine) (c : Config M.states) {small large : Nat}
    (h : HaltsFromWithin M c small) (hle : small ≤ large) : HaltsFromWithin M c large := by
  intro bits hbits
  have htake : (bits.take small).length = small := by
    simp [List.length_take, hbits, Nat.min_eq_left hle]
  have hh := h (bits.take small) htake
  have heq : M.run c bits = M.run c (bits.take small) := by
    conv_lhs => rw [← List.take_append_drop small bits]
    exact M.run_append_of_halted c _ _ hh
  rw [heq]
  exact hh

theorem compose_haltsFromWithin (M N : BinaryMachine) (c : Config M.states) (t₁ t₂ : Nat)
    (hfirst : HaltsFromWithin M c t₁)
    (hsecond : ∀ first : List Bool, first.length ≤ t₁ → HaltsAfter M c first →
      HaltsFromWithin N ⟨some N.initial, (M.run c first).«stacks»⟩ t₂) :
    HaltsFromWithin (compose M N) (liftLeft M N c) (t₁ + t₂) := by
  intro bits hbits
  have hlen : (bits.take t₁).length = t₁ := by
    simp [List.length_take, hbits]
  obtain ⟨first, leftover, heq, hf⟩ :=
    exists_halting_prefix M c (bits.take t₁) (hfirst _ hlen)
  have hfl : first.length ≤ t₁ := by
    have hh := congrArg List.length heq
    simp only [List.length_append, hlen] at hh
    omega
  have hwhole : bits = first ++ (leftover ++ bits.drop t₁) := by
    calc
      bits = bits.take t₁ ++ bits.drop t₁ := (List.take_append_drop t₁ bits).symm
      _ = first ++ (leftover ++ bits.drop t₁) := by rw [heq, List.append_assoc]
  have hremain : t₂ ≤ (leftover ++ bits.drop t₁).length := by
    have hh := congrArg List.length hwhole
    simp only [List.length_append] at hh
    simp only [List.length_append]
    omega
  have hn := haltsFromWithin_mono N _ (hsecond first hfl hf) hremain
  rw [hwhole]
  exact compose_halts M N c first _ hf (hn _ rfl)

theorem polynomialFuel_add_le (C₁ C₂ k₁ k₂ n : Nat) :
    polynomialFuel C₁ k₁ n + polynomialFuel C₂ k₂ n ≤
      polynomialFuel (C₁ + C₂) (max k₁ k₂) n := by
  have h₁ := Nat.pow_le_pow_right (by omega : 0 < n + 1) (Nat.le_max_left k₁ k₂)
  have h₂ := Nat.pow_le_pow_right (by omega : 0 < n + 1) (Nat.le_max_right k₁ k₂)
  unfold polynomialFuel
  calc
    _ ≤ C₁ * (n + 1) ^ max k₁ k₂ + C₂ * (n + 1) ^ max k₁ k₂ :=
      Nat.add_le_add (Nat.mul_le_mul_left C₁ h₁) (Nat.mul_le_mul_left C₂ h₂)
    _ = _ := (Nat.add_mul _ _ _).symm

theorem compose_polynomial (M N : BinaryMachine) (c : Config M.states)
    (C₁ C₂ k₁ k₂ n : Nat)
    (hfirst : HaltsFromWithin M c (polynomialFuel C₁ k₁ n))
    (hsecond : ∀ first : List Bool, first.length ≤ polynomialFuel C₁ k₁ n →
      HaltsAfter M c first →
      HaltsFromWithin N ⟨some N.initial, (M.run c first).«stacks»⟩ (polynomialFuel C₂ k₂ n)) :
    HaltsFromWithin (compose M N) (liftLeft M N c)
      (polynomialFuel (C₁ + C₂) (max k₁ k₂) n) :=
  haltsFromWithin_mono _ _
    (compose_haltsFromWithin M N c _ _ hfirst hsecond)
    (polynomialFuel_add_le C₁ C₂ k₁ k₂ n)

end Sequential
end KS.W29

end

end OAI
