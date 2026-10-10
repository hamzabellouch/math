import OAI.NumberTheory.Ostmann.Arithmetic.IntegerHistoryReconstruction

namespace OAI

namespace Ostmann

open scoped Classical

inductive BranchingWordHistory (σ : Type*) where
  | leaf (word : List σ)
  | node (step : HistoryPivotStep σ) (left right : BranchingWordHistory σ)

namespace BranchingWordHistory

variable {σ : Type*}

def Valid : BranchingWordHistory σ → (σ → ℤ) → Prop
  | .leaf _, _ => True
  | .node step left right, x =>
      step.Valid x ∧ left.Valid (step.applyInteger x) ∧ right.Valid (step.applyInteger x)

def flipSigned {α : Type*} (z : Bool × α) : Bool × α := (!z.1, z.2)

def mapSigned {α β : Type*} (f : α → β) (z : Bool × α) : Bool × β := (z.1, f z.2)

noncomputable def integerLeaves : BranchingWordHistory σ → (σ → ℤ) → List (Bool × ℤ)
  | .leaf word, x => [(true, (word.map x).prod)]
  | .node step left right, x =>
      left.integerLeaves (step.applyInteger x) ++
        (right.integerLeaves (step.applyInteger x)).map flipSigned

noncomputable def updatedFormulas (step : HistoryPivotStep σ) (env : σ → HistoryFormula σ) :
    σ → HistoryFormula σ :=
  Function.update env step.target (step.formula.bind env)

noncomputable def formulaLeaves : BranchingWordHistory σ → (σ → HistoryFormula σ) →
    List (Bool × HistoryFormula σ)
  | .leaf word, env => [(true, HistoryFormula.listProduct (word.map env))]
  | .node step left right, env =>
      left.formulaLeaves (updatedFormulas step env) ++
        (right.formulaLeaves (updatedFormulas step env)).map flipSigned

noncomputable def pivotFormulas : BranchingWordHistory σ → (σ → HistoryFormula σ) →
    List (HistoryFormula σ)
  | .leaf _, _ => []
  | .node step left right, env =>
      step.formula.bind env ::
        (left.pivotFormulas (updatedFormulas step env) ++
          right.pivotFormulas (updatedFormulas step env))

theorem wordFormula_value (word : List σ) (env : σ → HistoryFormula σ)
    (a : σ → ℚ) (x : σ → ℤ) (he : ∀ i, (env i).value a = x i) :
    (HistoryFormula.listProduct (word.map env)).value a = ((word.map x).prod : ℚ) := by
  rw [HistoryFormula.value_listProduct, List.map_map]
  simp only [Function.comp_def]
  have hmap : word.map (fun i => (env i).value a) = word.map (fun i => (x i : ℚ)) := by
    apply List.map_congr_left
    intro i _
    exact he i
  rw [hmap]
  clear hmap
  induction word with
  | nil => simp
  | cons i word ih => simpa only [List.map_cons, List.prod_cons, Int.cast_mul] using congrArg (fun z => (x i : ℚ) * z) ih

theorem updatedFormulas_value (step : HistoryPivotStep σ) (env : σ → HistoryFormula σ)
    (a : σ → ℚ) (x : σ → ℤ) (he : ∀ i, (env i).value a = x i) (hx : step.Valid x) :
    ∀ i, (updatedFormulas step env i).value a = (step.applyInteger x i : ℚ) := by
  have hstep : (step.formula.bind env).value a = (step.numerator x / step.s : ℤ) := by
    rw [HistoryFormula.value_bind]
    have he' : (fun i => (env i).value a) = fun i => (x i : ℚ) := funext he
    rw [he']
    exact step.formula_value_integer x hx
  intro i
  by_cases hi : i = step.target
  · subst i
    simpa only [updatedFormulas, HistoryPivotStep.applyInteger, Function.update_self] using hstep
  · simpa only [updatedFormulas, HistoryPivotStep.applyInteger, Function.update_of_ne hi] using he i

theorem mapSigned_flip {α β : Type*} (f : α → β) (l : List (Bool × α)) :
    (l.map flipSigned).map (mapSigned f) = (l.map (mapSigned f)).map flipSigned := by
  simp only [List.map_map]
  rfl

/-- Every signed leaf formula evaluates to its actual product after all
ancestor integer substitutions, including the independently replayed right branch. -/
theorem formulaLeaves_value (history : BranchingWordHistory σ) (env : σ → HistoryFormula σ)
    (a : σ → ℚ) (x : σ → ℤ) (he : ∀ i, (env i).value a = x i) (hx : history.Valid x) :
    (history.formulaLeaves env).map (mapSigned (fun F => F.value a)) =
      (history.integerLeaves x).map (mapSigned (fun z : ℤ => (z : ℚ))) := by
  induction history generalizing env x with
  | leaf word =>
    simp only [formulaLeaves, integerLeaves, List.map_cons, List.map_nil, mapSigned]
    rw [wordFormula_value word env a x he]
  | node step left right hl hr =>
    have hu := updatedFormulas_value step env a x he hx.1
    simp only [formulaLeaves, integerLeaves, List.map_append, mapSigned_flip]
    rw [hl _ _ hu hx.2.1, hr _ _ hu hx.2.2]

/-- Counts use the original branching structure, independent of assignments. -/
def leafCount : BranchingWordHistory σ → ℕ
  | .leaf _ => 1
  | .node _ left right => left.leafCount + right.leafCount

def nodeCount : BranchingWordHistory σ → ℕ
  | .leaf _ => 0
  | .node _ left right => 1 + left.nodeCount + right.nodeCount

theorem formulaLeaves_length (history : BranchingWordHistory σ) (env : σ → HistoryFormula σ) :
    (history.formulaLeaves env).length = history.leafCount := by
  induction history generalizing env with
  | leaf word => rfl
  | node step left right hl hr => simp only [formulaLeaves, List.length_append, List.length_map, hl, hr, leafCount]

theorem pivotFormulas_length (history : BranchingWordHistory σ) (env : σ → HistoryFormula σ) :
    (history.pivotFormulas env).length = history.nodeCount := by
  induction history generalizing env with
  | leaf word => rfl
  | node step left right hl hr =>
    simp only [pivotFormulas, List.length_cons, List.length_append, hl, hr, nodeCount]
    omega

end BranchingWordHistory
end Ostmann

end OAI
