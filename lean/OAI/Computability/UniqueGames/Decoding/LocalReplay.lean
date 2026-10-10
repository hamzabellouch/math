import Mathlib.Tactic.FinCases
import OAI.Computability.UniqueGames.Soundness.ConditionalLocality

namespace OAI

section

/-!
# Side-local replay of vanishing advice

The input-reconstruction step reuses the
elementary observation-fibre and Boolean-row infrastructure, not a repetition
bound or any inverse theorem.  The row index may be a disjoint union, so a
single row below represents both visible advice maps simultaneously.

We explicitly pass from the three equation bits to the two free homogeneous
coordinates.  The third position contributes `b * d` to the intercept and `d`
to both slopes.  At a clean position all three contributions vanish.  The
replay constructors take only the respective prover's clean questions; their
correctness is proved as equality of the complete question-and-row input.
-/

namespace UniqueGamesTheorem.Clean.LocalReplay

open Soundness
open Soundness.ConditionalIncidences

section Rows

variable {P R : Type}

/-- The three actual equation coordinates, including the homogeneous term. -/
def equationBit (b t x y : Bool) (i : Fin 3) : Bool :=
  if i = 0 then x else if i = 1 then y else (b && t) ^^ x ^^ y

theorem equationBit_satisfies (b t x y : Bool) :
    (equationBit b t x y 0 ^^ equationBit b t x y 1 ^^ equationBit b t x y 2) =
      (b && t) := by
  cases b <;> cases t <;> cases x <;> cases y <;> rfl

/-- The two free coordinates parameterize the entire homogeneous equation
space, not just its actual-answer slice `t = true`. -/
theorem equationBit_reconstruct (b t : Bool) (x : Fin 3 → Bool)
    (h : (x 0 ^^ x 1 ^^ x 2) = (b && t)) :
    equationBit b t (x 0) (x 1) = x := by
  have hthird : ((b && t) ^^ x 0 ^^ x 1) = x 2 := by
    cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;>
      cases b <;> cases t <;> simp_all
  funext i
  fin_cases i
  · simp [equationBit]
  · simp [equationBit]
  · simpa [equationBit] using hthird

/-- Pullback of a singleton column to the first free equation coordinate. -/
def singletonSlope₀ (d : ZeroInformation.Bits R) (i : Fin 3) : ZeroInformation.Bits R :=
  if i = 1 then ZeroInformation.zero else d

/-- Pullback of a singleton column to the second free equation coordinate. -/
def singletonSlope₁ (d : ZeroInformation.Bits R) (i : Fin 3) : ZeroInformation.Bits R :=
  if i = 0 then ZeroInformation.zero else d

/-- Only the third position changes the homogeneous intercept. -/
def singletonIntercept (d : ZeroInformation.Bits R) (i : Fin 3) (b : Bool) : ZeroInformation.Bits R :=
  if i = 2 then ZeroInformation.scale d b else ZeroInformation.zero

theorem singleton_pullback (d : ZeroInformation.Bits R) (i : Fin 3) (b t x y : Bool) :
    ZeroInformation.scale d (equationBit b t x y i) =
      ZeroInformation.add (ZeroInformation.scale (singletonIntercept d i b) t)
        (ZeroInformation.add (ZeroInformation.scale (singletonSlope₀ d i) x)
          (ZeroInformation.scale (singletonSlope₁ d i) y)) := by
  fin_cases i <;> funext r <;>
    cases hd : d r <;> cases b <;> cases t <;> cases x <;> cases y <;>
    simp [equationBit, singletonIntercept, singletonSlope₀, singletonSlope₁,
      ZeroInformation.scale, ZeroInformation.add, ZeroInformation.zero, hd]

@[simp] theorem singletonSlope₀_zero (i : Fin 3) :
    singletonSlope₀ (ZeroInformation.zero : ZeroInformation.Bits R) i = ZeroInformation.zero := by
  simp [singletonSlope₀]

@[simp] theorem singletonSlope₁_zero (i : Fin 3) :
    singletonSlope₁ (ZeroInformation.zero : ZeroInformation.Bits R) i = ZeroInformation.zero := by
  simp [singletonSlope₁]

@[simp] theorem singletonIntercept_zero (i : Fin 3) (b : Bool) :
    singletonIntercept (ZeroInformation.zero : ZeroInformation.Bits R) i b = ZeroInformation.zero := by
  simp [singletonIntercept]

/-- In particular the third-position right-hand side cannot survive a zero
singleton slope, even on arbitrary homogeneous vectors. -/
theorem third_position_clean (b t x y : Bool) :
    ZeroInformation.scale (ZeroInformation.zero : ZeroInformation.Bits R) (equationBit b t x y 2) = ZeroInformation.zero ∧
      singletonIntercept (ZeroInformation.zero : ZeroInformation.Bits R) 2 b = ZeroInformation.zero ∧
      singletonSlope₀ (ZeroInformation.zero : ZeroInformation.Bits R) 2 = ZeroInformation.zero ∧
      singletonSlope₁ (ZeroInformation.zero : ZeroInformation.Bits R) 2 = ZeroInformation.zero := by
  simp

private theorem add_zero (a : ZeroInformation.Bits R) : ZeroInformation.add a ZeroInformation.zero = a := by
  funext r
  change (a r ^^ false) = a r
  cases a r <;> rfl

private theorem zero_add (a : ZeroInformation.Bits R) : ZeroInformation.add ZeroInformation.zero a = a := by
  funext r
  change (false ^^ a r) = a r
  cases a r <;> rfl

private theorem add_assoc (a b c : ZeroInformation.Bits R) :
    ZeroInformation.add (ZeroInformation.add a b) c = ZeroInformation.add a (ZeroInformation.add b c) := by
  funext r
  change ((a r ^^ b r) ^^ c r) = (a r ^^ (b r ^^ c r))
  cases a r <;> cases b r <;> cases c r <;> rfl

private theorem add_shuffle (a b c d : ZeroInformation.Bits R) :
    ZeroInformation.add (ZeroInformation.add a b) (ZeroInformation.add c d) = ZeroInformation.add (ZeroInformation.add a c) (ZeroInformation.add b d) := by
  funext r
  change ((a r ^^ b r) ^^ (c r ^^ d r)) = ((a r ^^ c r) ^^ (b r ^^ d r))
  cases a r <;> cases b r <;> cases c r <;> cases d r <;> rfl

private theorem scale_add (a b : ZeroInformation.Bits R) (t : Bool) :
    ZeroInformation.scale (ZeroInformation.add a b) t = ZeroInformation.add (ZeroInformation.scale a t) (ZeroInformation.scale b t) := by
  funext r
  change ((a r ^^ b r) && t) = ((a r && t) ^^ (b r && t))
  cases a r <;> cases b r <;> cases t <;> rfl

private theorem rowSum_add (positions : List P) (a b : P → ZeroInformation.Bits R) :
    ZeroInformation.rowSum positions (fun j => ZeroInformation.add (a j) (b j)) =
      ZeroInformation.add (ZeroInformation.rowSum positions a) (ZeroInformation.rowSum positions b) := by
  induction positions with
  | nil => rfl
  | cons j positions ih =>
      change ZeroInformation.add (ZeroInformation.add (a j) (b j))
        (ZeroInformation.rowSum positions (fun j => ZeroInformation.add (a j) (b j))) =
          ZeroInformation.add (ZeroInformation.add (a j) (ZeroInformation.rowSum positions a))
            (ZeroInformation.add (b j) (ZeroInformation.rowSum positions b))
      rw [ih]
      exact add_shuffle _ _ _ _

private theorem rowSum_scale (positions : List P) (a : P → ZeroInformation.Bits R) (t : Bool) :
    ZeroInformation.rowSum positions (fun j => ZeroInformation.scale (a j) t) =
      ZeroInformation.scale (ZeroInformation.rowSum positions a) t := by
  induction positions with
  | nil => exact (ZeroInformation.scale_zero t).symm
  | cons j positions ih =>
      change ZeroInformation.add (ZeroInformation.scale (a j) t)
        (ZeroInformation.rowSum positions (fun j => ZeroInformation.scale (a j) t)) =
          ZeroInformation.scale (ZeroInformation.add (a j) (ZeroInformation.rowSum positions a)) t
      rw [ih, scale_add]

def interceptContribution (single : P → Bool) (d : P → ZeroInformation.Bits R)
    (indices : P → Fin 3) (rhs : P → Bool) : P → ZeroInformation.Bits R :=
  fun j => if single j then singletonIntercept (d j) (indices j) (rhs j) else ZeroInformation.zero

def paddedIntercept (positions : List P) (single : P → Bool) (c : ZeroInformation.Bits R)
    (d : P → ZeroInformation.Bits R) (indices : P → Fin 3) (rhs : P → Bool) : ZeroInformation.Bits R :=
  ZeroInformation.add c (ZeroInformation.rowSum positions (interceptContribution single d indices rhs))

def paddedSlope₀ (single : P → Bool) (full d : P → ZeroInformation.Bits R)
    (indices : P → Fin 3) : P → ZeroInformation.Bits R :=
  fun j => if single j then singletonSlope₀ (d j) (indices j) else full j

def paddedSlope₁ (single : P → Bool) (full d : P → ZeroInformation.Bits R)
    (indices : P → Fin 3) : P → ZeroInformation.Bits R :=
  fun j => if single j then singletonSlope₁ (d j) (indices j) else full j

/-- The full affine pullback, with the original intercept appearing exactly
once and every third-position correction explicitly included. -/
theorem full_padded_pullback (positions : List P) (single : P → Bool)
    (c : ZeroInformation.Bits R) (f₀ f₁ d : P → ZeroInformation.Bits R) (indices : P → Fin 3)
    (rhs : P → Bool) (t : Bool) (xy : P → Fin 2 → Bool) :
    ZeroInformation.pullbackRow positions single c f₀ f₁ d indices t
        (fun j => equationBit (rhs j) t (xy j 0) (xy j 1)) =
      ZeroInformation.add (ZeroInformation.scale (paddedIntercept positions single c d indices rhs) t)
        (ZeroInformation.rowSum positions fun j =>
          ZeroInformation.add (ZeroInformation.scale (paddedSlope₀ single f₀ d indices j) (xy j 0))
            (ZeroInformation.scale (paddedSlope₁ single f₁ d indices j) (xy j 1))) := by
  unfold ZeroInformation.pullbackRow
  have hterms : (fun j =>
      if single j then ZeroInformation.scale (d j) (equationBit (rhs j) t (xy j 0) (xy j 1) (indices j))
      else ZeroInformation.add (ZeroInformation.scale (f₀ j) (equationBit (rhs j) t (xy j 0) (xy j 1) 0))
        (ZeroInformation.scale (f₁ j) (equationBit (rhs j) t (xy j 0) (xy j 1) 1))) =
      (fun j => ZeroInformation.add (ZeroInformation.scale (interceptContribution single d indices rhs j) t)
        (ZeroInformation.add (ZeroInformation.scale (paddedSlope₀ single f₀ d indices j) (xy j 0))
          (ZeroInformation.scale (paddedSlope₁ single f₁ d indices j) (xy j 1)))) := by
    funext j
    cases hs : single j
    · simp [hs, interceptContribution, paddedSlope₀, paddedSlope₁, equationBit, zero_add]
    · simpa only [hs, ↓reduceIte, interceptContribution, paddedSlope₀, paddedSlope₁]
        using singleton_pullback (d j) (indices j) (rhs j) t (xy j 0) (xy j 1)
  rw [hterms, rowSum_add, rowSum_scale, ← add_assoc, ← scale_add]
  rfl

theorem clean_padded_columns (single : P → Bool) (f₀ f₁ d : P → ZeroInformation.Bits R)
    (indices : P → Fin 3) (rhs : P → Bool) (j : P)
    (hs : single j = true) (hz : d j = ZeroInformation.zero) :
    interceptContribution single d indices rhs j = ZeroInformation.zero ∧
      paddedSlope₀ single f₀ d indices j = ZeroInformation.zero ∧
      paddedSlope₁ single f₁ d indices j = ZeroInformation.zero := by
  simp [interceptContribution, paddedSlope₀, paddedSlope₁, hs, hz]

end Rows

noncomputable section

/-- The equation player's canonical two-free-coordinate advice input. -/
structure EquationInput (P R O : Type) where
  question : P → O
  row : Bool → (P → Fin 2 → Bool) → ZeroInformation.Bits R

/-- The variable player's input contains full occurrences or variable names,
with no occurrence attached to a singleton name. -/
structure VariableInput (P R O N : Type) where
  question : P → Sum O N
  row : Bool → (P → Fin 2 → Bool) → (P → Bool) → ZeroInformation.Bits R

def EquationInput.ofAmbient {P R O : Type} (rhs : O → Bool)
    (input : ZeroInformation.FirstInput P R O) : EquationInput P R O :=
  ⟨input.question, fun t xy => input.row t
    (fun j => equationBit (rhs (input.question j)) t (xy j 0) (xy j 1))⟩

def VariableInput.ofAmbient {P R O N : Type}
    (input : ZeroInformation.SecondInput P R O N) : VariableInput P R O N :=
  ⟨input.question, fun t xy y => input.row t
    (fun j i => if i = 0 then xy j 0 else if i = 1 then xy j 1 else false) y⟩

section Reconstruction

variable {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  (J : Finset P) (name : O → Fin 3 → N) (rhs : O → Bool)
  (gamma : RawCoefficients J (ZeroInformation.Bits R))
  (observed : PositionOutside (zeroSet J gamma) → O × N)

def actualEquationInput (sample : Draw P O) : EquationInput P R O :=
  EquationInput.ofAmbient rhs (actualFirst J gamma sample)

def actualVariableInput (sample : Draw P O) : VariableInput P R O N :=
  VariableInput.ofAmbient (actualSecond J name gamma sample)

/-- The reference is fixed public advice. The only remaining argument contains
the equation player's own clean equations; it contains no selected positions. -/
def replayEquationInput (reference : RawObservationFibre J name gamma observed)
    (insideEquations : PositionInside (zeroSet J gamma) → O) : EquationInput P R O :=
  EquationInput.ofAmbient rhs (localFirstFromH J name gamma observed reference insideEquations)

/-- The only remaining argument contains the variable player's own clean names;
it contains no clean equation or right-hand side. -/
def replayVariableInput (reference : RawObservationFibre J name gamma observed)
    (insideNames : PositionInside (zeroSet J gamma) → N) : VariableInput P R O N :=
  VariableInput.ofAmbient (localSecondFromH J name gamma observed reference insideNames)

theorem replayEquationInput_correct
    (distinct : ∀ o i i', name o i = name o i' → i = i')
    (reference sample : RawObservationFibre J name gamma observed) :
    replayEquationInput J name rhs gamma observed reference
        (fun j => (sample.val.2 j.val).1) =
      actualEquationInput J rhs gamma sample.val.2 := by
  unfold replayEquationInput actualEquationInput
  rw [localFirstFromH_correct J name gamma observed distinct reference sample]

omit [DecidableEq R] in
theorem replayVariableInput_correct
    (reference sample : RawObservationFibre J name gamma observed) :
    replayVariableInput J name gamma observed reference
        (fun j => name (sample.val.2 j.val).1 (sample.val.2 j.val).2) =
      actualVariableInput J name gamma sample.val.2 := by
  unfold replayVariableInput actualVariableInput
  rw [localSecondFromH_correct J name gamma observed reference sample]

/-- Equality of the equation player's own remaining questions implies equality
of its complete actual input, regardless of the clean selected positions. -/
theorem equation_input_independent_of_clean_positions
    (distinct : ∀ o i i', name o i = name o i' → i = i')
    (reference sample sample' : RawObservationFibre J name gamma observed)
    (sameEquations : ∀ j : PositionInside (zeroSet J gamma),
      (sample.val.2 j.val).1 = (sample'.val.2 j.val).1) :
    actualEquationInput J rhs gamma sample.val.2 =
      actualEquationInput J rhs gamma sample'.val.2 := by
  rw [← replayEquationInput_correct J name rhs gamma observed distinct reference sample,
    ← replayEquationInput_correct J name rhs gamma observed distinct reference sample']
  congr 1
  exact funext sameEquations

omit [DecidableEq R] in
/-- Equality of the variable player's own remaining questions implies equality
of its complete actual input, regardless of the clean equations. -/
theorem variable_input_independent_of_clean_equations
    (reference sample sample' : RawObservationFibre J name gamma observed)
    (sameNames : ∀ j : PositionInside (zeroSet J gamma),
      name (sample.val.2 j.val).1 (sample.val.2 j.val).2 =
        name (sample'.val.2 j.val).1 (sample'.val.2 j.val).2) :
    actualVariableInput J name gamma sample.val.2 =
      actualVariableInput J name gamma sample'.val.2 := by
  rw [← replayVariableInput_correct J name gamma observed reference sample,
    ← replayVariableInput_correct J name gamma observed reference sample']
  congr 1
  exact funext sameNames

end Reconstruction

end

end UniqueGamesTheorem.Clean.LocalReplay

end

end OAI
