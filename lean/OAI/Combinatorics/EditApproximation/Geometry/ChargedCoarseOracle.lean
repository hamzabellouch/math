import OAI.Combinatorics.EditApproximation.Geometry.ChargedGlobalQuery
import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryWork

namespace OAI

/-! All initial-entry information used by a charged table body arrives
through explicit requests. Flattening those requests gives an adaptive
coarse oracle program whose shape is independent of coarse answers. -/

namespace EditApproximation

namespace FiniteQuery

def substitute {ι κ : Type*} (ask : ι → FiniteQuery κ) : FiniteQuery ι → FiniteQuery κ
  | .done value => .done value
  | .read key next => bind (ask key) (fun value => substitute ask (next value))

theorem substitute_cost {ι κ : Type*} (ask : ι → FiniteQuery κ) (oracle : κ → ℚ)
    (weight : κ → ℕ) (query : FiniteQuery ι) :
    (query.substitute ask).cost oracle weight = query.cost
      (fun key => (ask key).value oracle) (fun key => (ask key).cost oracle weight) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    simp only [substitute, cost_bind, cost]
    exact congrArg ((ask key).cost oracle weight + ·) (ih ((ask key).value oracle))

theorem substitute_value {ι κ : Type*} (ask : ι → FiniteQuery κ) (oracle : κ → ℚ)
    (query : FiniteQuery ι) :
    (query.substitute ask).value oracle = query.value (fun key => (ask key).value oracle) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    simp only [substitute, bind_value, value]
    exact ih ((ask key).value oracle)

end FiniteQuery

section Coarse

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)

/-- An internal refinement body never inspects a coarse seed function
while building its local query. Its seed needs are explicit child reads. -/
theorem physicalGlobalQuery_refinement_initial_independent
    (left right : PhysicalEntry M J target.length → ℕ)
    (parent : PhysicalTableRequest M J target.length)
    (hi : ¬ parent.index ≤ T) (hd : parent.node.1.val < J)
    (hw : ¬ (physicalSourceInterval source.length parent.node).hi -
      (physicalSourceInterval source.length parent.node).lo ≤ 1) :
    physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer left parent =
    physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer right parent := by
  unfold physicalGlobalQuery
  dsimp only
  erw [dite_eq_right hi, dite_eq_right hi, dite_eq_left hd, dite_eq_left hd,
    dite_eq_right hw, dite_eq_right hw]

/-- Coarse answers enter the charged program only at coarse leaves. -/
theorem chargedGlobalQuery_table_initial_independent
    (left right : PhysicalEntry M J target.length → ℕ)
    (parent : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer left (.inr parent) =
    chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer right (.inr parent) := by
  unfold chargedGlobalQuery
  dsimp only
  split_ifs with hi hd hw
  · rfl
  · rfl
  · unfold physicalBoundedQuery restrictRankedProgram
    rw [physicalGlobalQuery_refinement_initial_independent source target N P F exponent H Q T S
      copies factor multiplier tau eta kappa delta group integer left right parent.val hi hd hw]
  · rfl

/-- The flattened program receives each coarse answer from an explicit
external read. The constant zero here is never used as a seed answer. -/
def chargedCoarseQuery (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    FiniteQuery (PhysicalEntry M J target.length) :=
  match root with
  | .inl entry => .read entry FiniteQuery.done
  | .inr parent =>
    (chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer (fun _ => 0) (.inr parent)).substitute
        (fun child => chargedCoarseQuery child.val)
termination_by root.rank
decreasing_by exact child.property

theorem chargedCoarseQuery_value
    (initial : PhysicalEntry M J target.length → ℕ)
    (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedCoarseQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer root).value (fun entry => (initial entry : ℚ)) =
    rankedProgramValue ChargedPhysicalRequest.rank
      (chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta group integer initial) root := by
  have hall : ∀ level root, root.rank = level →
      (chargedCoarseQuery source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta group integer root).value (fun entry => (initial entry : ℚ)) =
      rankedProgramValue ChargedPhysicalRequest.rank
        (chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
          tau eta kappa delta group integer initial) root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hlevel
      cases root with
      | inl entry =>
        rw [chargedCoarseQuery, rankedProgramValue]
        rfl
      | inr parent =>
        rw [chargedCoarseQuery, FiniteQuery.substitute_value, rankedProgramValue,
          chargedGlobalQuery_table_initial_independent source target N P F exponent H Q T S passes copies
            factor multiplier tau eta kappa delta group integer (fun _ => 0) initial parent]
        congr 1
        funext child
        exact ih child.val.rank (hlevel ▸ child.property) child.val rfl
  exact hall root.rank root rfl

end Coarse

end EditApproximation

end OAI
