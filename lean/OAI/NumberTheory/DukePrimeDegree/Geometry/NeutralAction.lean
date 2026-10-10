import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralDiagonal

namespace OAI

/-!
# The neutral diagonal action on the lattice quotient

The concrete neutral weight subgroup acts continuously by right diagonal
translations. Its measure-preserving action follows from full diagonal
invariance, and every trace-zero neutral weight is represented in it.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

@[instance_reducible] def neutralDiagonalAction {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MulAction (Multiplicative (neutralWeightSubgroup i j)) (X n) :=
  let := rightSubgroupAction (rootPairCentralizer hij)
  MulAction.compHom (X n) (neutralDiagonalOppositeHom hij)

lemma neutralDiagonalAction_continuous {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    let := neutralDiagonalAction hij
    ContinuousSMul (Multiplicative (neutralWeightSubgroup i j)) (X n) := by
  let := neutralDiagonalAction hij
  constructor
  exact (continuous_rightAction_uncurry n).comp
    (continuous_snd.prodMk
      ((continuous_subtype_val.comp (continuous_neutralDiagonalHom hij)).comp continuous_fst))

lemma neutralDiagonalAction_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (u : Multiplicative (neutralWeightSubgroup i j)) (x : X n) :
    let := neutralDiagonalAction hij
    u • x = rightAction x (diagonalOneParameter u.toAdd.val u.toAdd.property.1 1) := rfl

lemma neutralDiagonal_preserving
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1)))
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (u : Multiplicative (neutralWeightSubgroup i j)) :
    let := neutralDiagonalAction hij
    MeasurePreserving (fun x : X (d + 1) => u • x) μ μ := by
  let := neutralDiagonalAction hij
  refine ⟨(continuous_rightAction _).measurable, ?_⟩
  change μ.map (fun x => rightAction x (diagonalOneParameter u.toAdd.val u.toAdd.property.1 1)) = μ
  rw [diagonalOneParameter_eq_diagonalFlow]
  exact hA _

lemma neutralDiagonal_apply_weights {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ a, ell a = 0) (hneutral : ell i = ell j) (x : X n) :
    let := neutralDiagonalAction hij
    Multiplicative.ofAdd (⟨ell, hell, hneutral⟩ : neutralWeightSubgroup i j) • x =
      rightAction x (diagonalOneParameter ell hell 1) := rfl

end DukePrimeDegree

end

end OAI
