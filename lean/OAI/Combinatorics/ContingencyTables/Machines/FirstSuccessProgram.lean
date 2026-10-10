import OAI.Combinatorics.ContingencyTables.Machines.ListWordProgram
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordRejection

namespace OAI

/-! # Polynomial first-success selection for a supplied list of trial words -/

namespace ContingencyTables.FirstSuccessProgram
open MatchingFPRAS.TreeTyped

variable {A B W : Type} [Codec A] [Codec B] [Codec W] [Inhabited B]

def firstSome : List (Option B) → Option B
  | [] => none
  | none::xs => firstSome xs
  | Option.some x::_ => Option.some x

def isSomeRealizer : Realizer (Option.isSome : Option B → Bool) :=
  (composition (pair (constant false) identity)
    (optionCases (constant false) (constant true))).congr (by intro o; cases o <;> rfl)

theorem polynomial_isSome : PolynomialTime (isSomeRealizer (B := B)) := by
  unfold isSomeRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair (polynomial_constant false) polynomial_identity)
    (polynomial_optionCases (polynomial_constant false) (polynomial_constant true))

omit [Codec B] [Inhabited B] in
lemma firstSome_filter (xs : List (Option B)) :
    (xs.filter Option.isSome).headD none=firstSome xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | none => exact ih
    | some b => rfl

def firstSomeRealizer : Realizer (firstSome (B := B)) :=
  (composition (filter isSomeRealizer) (head none)).congr firstSome_filter

theorem polynomial_firstSome : PolynomialTime (firstSomeRealizer (B := B)) :=
  polynomial_congr _ (polynomial_composition (polynomial_filter polynomial_isSome) (polynomial_head none))

def defaultRealizer : Realizer (fun z : B×Option B => z.2.getD z.1) :=
  (optionCases identity second).recode id (fun z : B×Option B => z.2.getD z.1)
    (fun _ => rfl) (by rintro ⟨b,o⟩; cases o <;> rfl)

theorem polynomial_default : PolynomialTime (defaultRealizer (B := B)) := by
  unfold defaultRealizer
  apply polynomial_recode
  exact polynomial_optionCases polynomial_identity polynomial_second

def retry (f : A×W → Option B) (z : (A×B)×List W) : B :=
  (firstSome (z.2.map (fun w => f (z.1.1,w)))).getD z.1.2

def retryRealizer {f : A×W → Option B} (F : Realizer f) : Realizer (retry f) := by
  let inputs : Realizer (fun z : (A×B)×List W => (z.1.1,z.2)) :=
    pair (composition first first) second
  let results := composition inputs (mapWith F)
  exact composition (pair (composition first second) (composition results firstSomeRealizer)) defaultRealizer

theorem polynomial_retry {f : A×W → Option B} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (retryRealizer F) := by
  unfold retryRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_mapWith hF)) polynomial_firstSome)) polynomial_default

noncomputable section
open scoped Classical

omit [Codec A] [Codec B] [Inhabited B] in
theorem retry_ofFn {k n : ℕ} (f : A×List Bool → Option B)
    (a : A) (fallback : B) (bits : Fin n → Fin k → Bool) :
    retry f ((a,fallback),List.ofFn (fun i => List.ofFn (bits i)))=
      FirstSuccess.wordRetry (fun word => f (a,List.ofFn word)) fallback n bits := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [retry,List.ofFn_succ,List.map_cons,FirstSuccess.wordRetry]
    cases h : f (a,List.ofFn (bits 0)) with
    | none =>
      simp only [firstSome,Option.getD_none]
      exact ih (Fin.tail bits)
    | some b => simp only [firstSome,Option.getD_some]

theorem wordRetry_map {α β : Type*} {k : ℕ} (f : (Fin k → Bool) → Option α)
    (g : α → β) (fallback : α) (n : ℕ) (bits : Fin n → Fin k → Bool) :
    FirstSuccess.wordRetry (fun word => (f word).map g) (g fallback) n bits=
      g (FirstSuccess.wordRetry f fallback n bits) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [FirstSuccess.wordRetry]
    cases f (bits 0) with
    | none => simpa only [Option.map_none,Option.getD_none] using ih (Fin.tail bits)
    | some x => rfl

end
end ContingencyTables.FirstSuccessProgram

end OAI
