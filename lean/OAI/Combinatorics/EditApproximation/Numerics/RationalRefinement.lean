import OAI.Combinatorics.EditApproximation.Geometry.Bellman
import OAI.Combinatorics.EditApproximation.Geometry.Cones
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Rational execution of the Bellman and refinement operations

Every finite minimum, cone cost, warmup iteration, and refinement update
is computed in rational arithmetic. The real analysis used elsewhere is
the exact cast of these operations. An absent online candidate returns
the cone minimum, avoiding an extended-real value in the implementation.
-/

namespace EditApproximation



theorem rationalMinimum_cast (fallback : ℚ) (values : List ℚ) :
    (rationalMinimum fallback values : ℝ) = finiteMinimum (fallback : ℝ) (values.map Rat.cast) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [rationalMinimum, finiteMinimum, List.map_cons, Rat.cast_min, ih]



def RationalBellmanAction.toReal {Parent Child : Type*} {M : ℕ}
    (action : RationalBellmanAction Parent Child M) : BellmanAction Parent Child M :=
  ⟨action.center, action.connection, action.childState⟩





theorem rationalActionValue_cast {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → ℚ) (L : ℚ) (child : Child → ℚ)
    (query : Parent) (action : RationalBellmanAction Parent Child M) :
    (rationalActionValue distance L child query action : ℝ) =
      bellmanActionValue (fun q r => (distance q r : ℝ)) (L : ℝ)
        (fun s => (child s : ℝ)) query action.toReal := by
  simp only [rationalActionValue, bellmanActionValue, RationalBellmanAction.toReal,
    Rat.cast_add, Rat.cast_mul, Rat.cast_sum]

theorem rationalBellman_cast {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℚ) (distance : Parent → Parent → ℚ) (L : ℚ)
    (actions : List (RationalBellmanAction Parent Child M)) (child : Child → ℚ) (query : Parent) :
    (rationalBellman fallback distance L actions child query : ℝ) =
      finiteBellman (fun q => (fallback q : ℝ)) (fun q r => (distance q r : ℝ)) (L : ℝ)
        (actions.map RationalBellmanAction.toReal) (fun s => (child s : ℝ)) query := by
  rw [rationalBellman, rationalMinimum_cast]
  unfold finiteBellman
  simp only [List.map_map, Function.comp_def, rationalActionValue_cast]

def rationalWarmup {State : Type*} (operator : (State → ℚ) → State → ℚ)
    (initial : State → ℚ) : ℕ → State → ℚ
  | 0 => initial
  | t + 1 => operator (rationalWarmup operator initial t)

theorem rationalWarmup_cast {State : Type*}
    (operator : (State → ℚ) → State → ℚ) (realOperator : (State → ℝ) → State → ℝ)
    (initial : State → ℚ)
    (hoperator : ∀ value q, (operator value q : ℝ) = realOperator (fun s => (value s : ℝ)) q)
    (t : ℕ) (q : State) :
    (rationalWarmup operator initial t q : ℝ) = warmup realOperator (fun s => (initial s : ℝ)) t q := by
  induction t generalizing q with
  | zero => rfl
  | succ t ih =>
    rw [rationalWarmup, warmup, hoperator]
    congr 1
    funext s
    exact ih s



theorem rationalRefinementUpdate_cast (δ cone online : ℚ) :
    (rationalRefinementUpdate δ cone (some online) : ℝ) =
      refinementUpdate (δ : ℝ) (cone : ℝ) (online : ℝ) := by
  simp only [rationalRefinementUpdate, refinementUpdate, Rat.cast_min, Rat.cast_max,
    Rat.cast_div, Rat.cast_add, Rat.cast_one]

theorem rationalRefinementUpdate_none (δ cone : ℚ) :
    rationalRefinementUpdate δ cone none = cone := rfl

end EditApproximation

end OAI
