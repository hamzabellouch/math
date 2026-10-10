import Mathlib
import OAI.Computability.MaxCut.Encoding.Encoding2
import OAI.Computability.MaxCut.Games.Incidence

namespace OAI

namespace MaxCutGames.Reduction.CloneTable

open CloneGap ActualSource

variable {n : Nat}

/-- A total bounded-name helper. Every index used by the table is below 48,
    and `cloneName_value` removes the remainder operation on those indices. -/
def cloneName (v : Fin n) (i : Nat) : Fin (n * 48) :=
  ⟨i % 48 + 48 * v.val, by
    have hi := Nat.mod_lt i (show 0 < 48 by decide)
    have hv := v.isLt
    omega⟩

theorem cloneName_value (v : Fin n) (i : Nat) (hi : i < 48) :
    (cloneName v i).val = i + 48 * v.val := by
  simp only [cloneName, Nat.mod_eq_of_lt hi]

def cloneEquation (e : Equation (Fin n)) (t : Nat × Nat × Nat) :
    Equation (Fin (n * 48)) :=
  ⟨cloneName e.first t.1, cloneName e.second t.2.1,
    cloneName e.third t.2.2, e.rhs⟩

def clonedEquations (es : List (Equation (Fin n))) : List (Equation (Fin (n * 48))) :=
  es.flatMap fun e => distinctTriples.map (cloneEquation e)

private theorem length_flatMap_map_inline_CloneTable {α β γ : Type*}
    (xs : List α) (ys : List β) (f : α → β → γ) :
    (xs.flatMap fun x => ys.map (f x)).length = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
      rw [ih]
      simp [Nat.add_mul, Nat.add_comm]

theorem clonedEquations_length (es : List (Equation (Fin n))) :
    (clonedEquations es).length = es.length * distinctTriples.length := by
  exact length_flatMap_map_inline_CloneTable es distinctTriples cloneEquation

theorem clonedEquations_nonempty (es : List (Equation (Fin n))) (hne : es ≠ []) :
    clonedEquations es ≠ [] := by
  apply List.length_pos_iff.mp
  rw [clonedEquations_length]
  exact Nat.mul_pos (List.length_pos_iff.mpr hne) FiniteSource.distinctTriples_nonempty

/-- Exact equality of typed ordered lists, not just permutation or equal counts. -/
theorem cloned_sourceList (S : Source) :
    (FiniteSource.cloned S).sourceList = clonedEquations S.sourceList := by
  let encode : Equation (Fin S.«variables» × Nat) → Equation (Fin (S.«variables» * 48)) :=
    fun e => FiniteSource.mapEquation (fun z => cloneName z.1 z.2) e
  have hmap : (FiniteSource.cloned S).sourceList = (cloneList S.sourceList).map encode := by
    have hm := congrArg (List.map encode)
      (List.ofFn_getElem (xs := cloneList S.sourceList))
    change List.ofFn (fun i : Fin (cloneList S.sourceList).length =>
      encode (cloneList S.sourceList)[i.val]) = _
    simpa only [List.map_ofFn, Function.comp_def] using hm
  rw [hmap]
  simp only [cloneList, clonedEquations, List.map_flatMap, List.map_map, Function.comp_def]
  rfl

theorem cloned_ofList_sourceList (es : List (Equation (Fin n))) (hne : es ≠ []) :
    (FiniteSource.cloned (Source.ofList es hne)).sourceList = clonedEquations es := by
  rw [cloned_sourceList, Source.sourceList_ofList]
  rfl

theorem source_reconstructed (S : Source) :
    Source.ofList S.sourceList S.sourceList_nonempty = S := by
  cases S with
  | mk n m hm eqn =>
      simp only [Source.ofList, Source.sourceList]
      erw [Source.mk.injEq]
      refine ⟨rfl, List.length_ofFn, ?_⟩
      apply (Fin.heq_fun_iff List.length_ofFn).mpr
      intro i
      simp only [List.get_eq_getElem, List.getElem_ofFn]

private theorem ofList_congr_inline_CloneTable {es fs : List (Equation (Fin n))}
    (he : es = fs) (hne : es ≠ []) (hnf : fs ≠ []) :
    Source.ofList es hne = Source.ofList fs hnf := by
  cases he
  rfl

def eraseEquation (e : Equation (Fin n)) : Equation Nat :=
  ⟨e.first.val, e.second.val, e.third.val, e.rhs⟩

/-- Numeric machine target: no remainder, bounded-name proofs, or function
    lookup is needed in the three generated variable names. -/
def natCloneEquation (e : Equation Nat) (t : Nat × Nat × Nat) : Equation Nat :=
  ⟨t.1 + 48 * e.first, t.2.1 + 48 * e.second, t.2.2 + 48 * e.third, e.rhs⟩

def natClonedEquations (es : List (Equation Nat)) : List (Equation Nat) :=
  es.flatMap fun e => distinctTriples.map (natCloneEquation e)

theorem erase_cloneEquation (e : Equation (Fin n)) (t : Nat × Nat × Nat)
    (ht : t ∈ distinctTriples) :
    eraseEquation (cloneEquation e t) = natCloneEquation (eraseEquation e) t := by
  obtain ⟨h₁, h₂, h₃⟩ := FiniteSource.distinctTriple_bounds ht
  simp only [eraseEquation, cloneEquation, natCloneEquation, cloneName,
    Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂, Nat.mod_eq_of_lt h₃]

theorem erase_clonedEquations (es : List (Equation (Fin n))) :
    (clonedEquations es).map eraseEquation = natClonedEquations (es.map eraseEquation) := by
  simp only [clonedEquations, natClonedEquations, List.map_flatMap, List.map_map,
    List.flatMap_map, Function.comp_def]
  apply List.flatMap_congr
  intro e _
  apply List.map_congr_left
  intro t ht
  exact erase_cloneEquation e t ht

def cloneEquationWords (e : Equation (Fin n)) (t : Nat × Nat × Nat) : List Nat :=
  [t.1 + 48 * e.first.val, t.2.1 + 48 * e.second.val,
    t.2.2 + 48 * e.third.val, if e.rhs then 1 else 0]

def clonedBodyWords (es : List (Equation (Fin n))) : List Nat :=
  es.flatMap fun e => distinctTriples.flatMap (cloneEquationWords e)

theorem cloneEquation_words (e : Equation (Fin n)) (t : Nat × Nat × Nat)
    (ht : t ∈ distinctTriples) :
    SourceEncoding.equationWords (cloneEquation e t) = cloneEquationWords e t := by
  obtain ⟨h₁, h₂, h₃⟩ := FiniteSource.distinctTriple_bounds ht
  simp only [SourceEncoding.equationWords, cloneEquationWords, cloneEquation, cloneName,
    Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂, Nat.mod_eq_of_lt h₃]

theorem clonedEquations_words (es : List (Equation (Fin n))) :
    (clonedEquations es).flatMap SourceEncoding.equationWords = clonedBodyWords es := by
  simp only [clonedEquations, clonedBodyWords, List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro e _
  apply List.flatMap_congr
  intro t ht
  exact cloneEquation_words e t ht

def clonedInput (input : SourceEncoding.Input) : SourceEncoding.Input where
  «variables» := input.«variables» * 48
  equations := clonedEquations input.equations
  nonempty := clonedEquations_nonempty input.equations input.nonempty

def clonedInputWords (input : SourceEncoding.Input) : List Nat :=
  [input.«variables» * 48, input.equations.length * distinctTriples.length] ++
    clonedBodyWords input.equations

theorem clonedInput_equations (input : SourceEncoding.Input) :
    (clonedInput input).equations =
      (FiniteSource.cloned (Source.ofList input.equations input.nonempty)).sourceList := by
  exact (cloned_ofList_sourceList input.equations input.nonempty).symm

theorem clonedInput_source (input : SourceEncoding.Input) :
    Source.ofList (clonedInput input).equations (clonedInput input).nonempty =
      FiniteSource.cloned (Source.ofList input.equations input.nonempty) := by
  have hs := source_reconstructed
    (FiniteSource.cloned (Source.ofList input.equations input.nonempty))
  have he := clonedInput_equations input
  exact (ofList_congr_inline_CloneTable he _ _).trans hs

theorem clonedInput_words (input : SourceEncoding.Input) :
    SourceEncoding.inputWords (clonedInput input) = clonedInputWords input := by
  simp only [SourceEncoding.inputWords, clonedInput, clonedInputWords,
    clonedEquations_length, clonedEquations_words]

theorem clonedInput_decodes (input : SourceEncoding.Input) :
    SourceEncoding.decodeInputWords (clonedInputWords input) = some (clonedInput input) := by
  rw [← clonedInput_words]
  exact SourceEncoding.decodeInputWords_encoded _

/-- A size bound for the actual serialized intermediate table. This is not
    a machine-time bound. -/
theorem clonedInput_bits_length_le (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (clonedInput input)).length ≤
      48 * input.«variables» + distinctTriples.length * input.equations.length + 2 +
        distinctTriples.length * input.equations.length * (144 * input.«variables» + 2) := by
  calc
    _ ≤ (clonedInput input).«variables» + (clonedInput input).equations.length + 2 +
        (clonedInput input).equations.length * (3 * (clonedInput input).«variables» + 2) :=
      SourceEncoding.inputBits_length_le _
    _ = _ := by
      simp only [clonedInput, clonedEquations_length]
      ring

end MaxCutGames.Reduction.CloneTable

end OAI
