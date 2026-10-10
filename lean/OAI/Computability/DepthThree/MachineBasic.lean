import OAI.Computability.DepthThree.Model

namespace OAI

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7 uDepth8 uDepth9 uDepth10 uDepth11 uDepth12

namespace DepthThreeLowerBound

@[simp] theorem runSteps_zero {S : Type uDepth1} (step : S → Option S) (c : Option S) :
    runSteps step 0 c = c := rfl

theorem runSteps_succ {S : Type uDepth2} (step : S → Option S) (n : ℕ) (c : Option S) :
    runSteps step (n + 1) c = (runSteps step n c).bind step := by
  exact Function.iterate_succ_apply' _ _ _

theorem runSteps_succ_left {S : Type uDepth3} (step : S → Option S) (n : ℕ)
    (c : Option S) :
    runSteps step (n + 1) c = runSteps step n (c.bind step) := by
  exact Function.iterate_succ_apply _ _ _

@[simp] theorem runSteps_none {S : Type uDepth4} (step : S → Option S) (n : ℕ) :
    runSteps step n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runSteps_succ, ih]; rfl

theorem runSteps_add {S : Type uDepth5} (step : S → Option S) (m n : ℕ) (c : Option S) :
    runSteps step (m + n) c = runSteps step m (runSteps step n c) := by
  exact Function.iterate_add_apply _ _ _ _

theorem runSteps_succ_eq_of_step_eq {S : Type uDepth6} {step : S → Option S}
    {a b : S} (h : step a = step b) (n : ℕ) :
    runSteps step (n + 1) (some a) = runSteps step (n + 1) (some b) := by
  rw [runSteps_succ_left, runSteps_succ_left]
  exact congrArg (runSteps step n) h

theorem runSteps_eq_of_step_eq {S : Type uDepth7} {step : S → Option S}
    {a b : S} (h : step a = step b) {n : ℕ} (hn : 0 < n) :
    runSteps step n (some a) = runSteps step n (some b) := by
  cases n with
  | zero => exact False.elim ((Nat.not_lt_zero 0) hn)
  | succ n => exact runSteps_succ_eq_of_step_eq h n

def RunsIn {S : Type uDepth8} (step : S → Option S) (a b : S) (bound : ℕ) : Prop :=
  ∃ n ≤ bound, runSteps step n (some a) = some b

theorem RunsIn.refl {S : Type uDepth9} (step : S → Option S) (a : S) :
    RunsIn step a a 0 :=
  ⟨0, le_refl 0, rfl⟩

theorem RunsIn.single {S : Type uDepth10} {step : S → Option S} {a b : S}
    (h : step a = some b) : RunsIn step a b 1 :=
  ⟨1, le_refl 1, h⟩

theorem RunsIn.mono {S : Type uDepth11} {step : S → Option S} {a b : S} {m n : ℕ}
    (h : RunsIn step a b m) (hmn : m ≤ n) : RunsIn step a b n := by
  obtain ⟨k, hk, he⟩ := h
  exact ⟨k, hk.trans hmn, he⟩

theorem RunsIn.trans {S : Type uDepth12} {step : S → Option S} {a b c : S} {m n : ℕ}
    (h₁ : RunsIn step a b m) (h₂ : RunsIn step b c n) :
    RunsIn step a c (m + n) := by
  obtain ⟨k₁, hk₁, he₁⟩ := h₁
  obtain ⟨k₂, hk₂, he₂⟩ := h₂
  refine ⟨k₂ + k₁, ?_, ?_⟩
  · simpa only [Nat.add_comm] using Nat.add_le_add hk₂ hk₁
  · rw [runSteps_add, he₁]
    exact he₂

structure FiniteMachine where
  Γ : Type
  [alphabetInhabited : Inhabited Γ]
  [alphabetFinite : Fintype Γ]
  Λ : Type
  [stateInhabited : Inhabited Λ]
  [stateFinite : Fintype Λ]
  inputSymbol : Bool → Γ
  input_injective : Function.Injective inputSymbol
  input_ne_blank : ∀ b, inputSymbol b ≠ default
  code : Turing.TM0.Machine Γ Λ
  accept : Λ → Bool

attribute [instance] FiniteMachine.alphabetInhabited FiniteMachine.alphabetFinite
  FiniteMachine.stateInhabited FiniteMachine.stateFinite

def HaltsIn (M : FiniteMachine) (input : List Bool) (output : Bool) (time : ℕ) : Prop :=
  ∃ k ≤ time, ∃ c : Turing.TM0.Cfg M.Γ M.Λ,
    runSteps (Turing.TM0.step M.code) k
      (some (Turing.TM0.init (input.map M.inputSymbol))) = some c ∧
    Turing.TM0.step M.code c = none ∧ M.accept c.q = output

def PolynomialTimeDecider (f : List Bool → Bool) : Prop :=
  ∃ M : FiniteMachine, ∃ C a : ℕ, 0 < C ∧ 0 < a ∧
    ∀ w, HaltsIn M w (f w) (C * (w.length + 1) ^ a)

end DepthThreeLowerBound

end OAI
