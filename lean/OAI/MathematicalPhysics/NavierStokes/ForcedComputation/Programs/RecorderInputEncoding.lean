import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FiniteRecorder
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ConfigurationTapes
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RationalEncoding

namespace OAI

/-! The initialized recorder point is computable from a finite rational word. -/

namespace ForcedComputation.Radix

theorem prependWord_ofFn_eq {A : Type*} (u : ℕ → A) (blank : A) (N : ℕ)
    (ht : ∀ n, N ≤ n → u n = blank) :
    prependWord (List.ofFn (fun i : Fin N => u i)) (fun _ => blank) = u := by
  induction N generalizing u with
  | zero =>
    funext n
    simpa only [List.ofFn_zero, prependWord] using (ht n (Nat.zero_le n)).symm
  | succ N ih =>
    rw [List.ofFn_succ]
    funext n
    cases n with
    | zero => rfl
    | succ n =>
      change prependWord (List.ofFn (fun i : Fin N => u (i.val + 1))) (fun _ => blank) n = _
      exact congrFun (ih (fun k => u (k + 1)) (fun k hk => ht (k + 1) (by omega))) n

end ForcedComputation.Radix

namespace ForcedComputation.Recorder

open Radix

def recorderBlank (M : Alternating.Machine) : Symbol (State M) (Alphabet M) :=
  (⟨0, by simp [Alternating.Machine.symbolCount]⟩, History.empty, false)

def initialWordLength (I : Alternating.MachineInput) : ℕ := max I.2.length 3

def initialRightWord (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    List (Symbol (State I.1) (Alphabet I.1)) :=
  List.ofFn fun i : Fin (initialWordLength I) => (finiteInitializedRecorder I hI).tape i.val

theorem initialTape_blank (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {j : ℤ} (hj : j < 0 ∨ (initialWordLength I : ℤ) ≤ j) :
    (finiteInitializedRecorder I hI).tape j = recorderBlank I.1 := by
  have hjdata : j < 0 ∨ (I.2.length : ℤ) ≤ j := by
    rcases hj with hj | hj
    · exact Or.inl hj
    · right
      have hlen : I.2.length ≤ initialWordLength I := le_max_left _ _
      exact (by exact_mod_cast hlen : (I.2.length : ℤ) ≤ initialWordLength I).trans hj
  have hjfront : j ≠ 2 := by
    have hlen : 3 ≤ initialWordLength I := le_max_right _ _
    rcases hj with hj | hj <;> omega
  have hd := Alternating.initialConfiguration_tape_outside I.2 hjdata
  change (initialAlphabet I hI j, historyRun 2
    (workRecord (finiteMachine I.1 hI.1) (initialState I.1) (initialAlphabet I hI)) 0 j, false) = _
  apply Prod.ext
  · apply Fin.ext
    exact hd
  · simp [historyRun, recorderBlank, Function.update_of_ne hjfront]

theorem initialTape_left (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    (tapeAt (finiteInitializedRecorder I hI)).1 = fun _ => recorderBlank I.1 := by
  funext n
  apply initialTape_blank I hI
  left
  change (0 : ℤ) - ((n : ℤ) + 1) < 0
  omega

theorem initialTape_right (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    (tapeAt (finiteInitializedRecorder I hI)).2 =
      prependWord (initialRightWord I hI) (fun _ => recorderBlank I.1) := by
  symm
  have hhead : (finiteInitializedRecorder I hI).head = 0 := rfl
  change prependWord (List.ofFn (fun i : Fin (initialWordLength I) =>
    (finiteInitializedRecorder I hI).tape i.val)) (fun _ => recorderBlank I.1) =
      fun n : ℕ => (finiteInitializedRecorder I hI).tape
        ((finiteInitializedRecorder I hI).head + (n : ℤ))
  simp only [hhead, zero_add]
  apply prependWord_ofFn_eq (fun n : ℕ => (finiteInitializedRecorder I hI).tape n)
    (recorderBlank I.1) (initialWordLength I)
  intro n hn
  apply initialTape_blank I hI
  right
  exact_mod_cast hn

theorem initial_coordinates_rational (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {B : ℚ} (hB : 1 < B) {digit : Symbol (State I.1) (Alphabet I.1) → ℚ}
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) :
    coordinates B (fun a => (digit a : ℝ)) (tapeAt (finiteInitializedRecorder I hI)) =
      (((digit (recorderBlank I.1) / (B - 1) : ℚ) : ℝ),
        ((finiteCode B digit (initialRightWord I hI) (recorderBlank I.1) : ℚ) : ℝ)) := by
  have hBr : (1 : ℝ) < B := by exact_mod_cast hB
  have hdr : ∀ a, (0 : ℝ) ≤ digit a ∧ (digit a : ℝ) ≤ (B : ℝ) - 1 := by
    intro a
    constructor
    · exact_mod_cast (hd a).1
    · exact_mod_cast (hd a).2
  apply Prod.ext
  · change encode B (fun a => (digit a : ℝ)) (tapeAt (finiteInitializedRecorder I hI)).1 = _
    rw [initialTape_left, encode_const hBr hdr]
    simp
  · change encode B (fun a => (digit a : ℝ)) (tapeAt (finiteInitializedRecorder I hI)).2 = _
    rw [initialTape_right]
    exact finiteCode_spec hB hd _ _

end ForcedComputation.Recorder

end OAI
