import OAI.NumberTheory.DukePrimeDegree.Dynamics.CentralizerFlow
import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientNeighborhoods

namespace OAI

/-!
# The neutral diagonal group

The kernel of one root character, inside trace-zero real weights, is the
group used for the ergodic decomposition in EKL's low-entropy argument.
Its diagonal representation takes values in the opposite-root centralizer.
-/

noncomputable section
open Set Matrix
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def neutralWeightSubgroup {n : ℕ} (i j : Fin n) : AddSubgroup (Fin n → ℝ) where
  carrier := {ell | (∑ r, ell r) = 0 ∧ ell i = ell j}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, hai⟩ ⟨hb, hbi⟩
    constructor
    · simp only [Pi.add_apply, Finset.sum_add_distrib, ha, hb, add_zero]
    · simp only [Pi.add_apply, hai, hbi]
  neg_mem' := by
    rintro a ⟨ha, hai⟩
    constructor
    · simp only [Pi.neg_apply, Finset.sum_neg_distrib, ha, neg_zero]
    · simp only [Pi.neg_apply, hai]

lemma diagonalOneParameter_add_weights {n : ℕ}
    (a b : Fin n → ℝ) (ha : ∑ r, a r = 0) (hb : ∑ r, b r = 0) (t : ℝ) :
    diagonalOneParameter (a + b)
      (by simp only [Pi.add_apply, Finset.sum_add_distrib, ha, hb, add_zero]) t =
      diagonalOneParameter a ha t * diagonalOneParameter b hb t := by
  apply Subtype.ext
  change Matrix.diagonal (fun r => Real.exp ((a r + b r) * t)) =
    Matrix.diagonal (fun r => Real.exp (a r * t)) * Matrix.diagonal (fun r => Real.exp (b r * t))
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext r
  simp only [add_mul, Real.exp_add]

def neutralDiagonalHom {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Multiplicative (neutralWeightSubgroup i j) →* rootPairCentralizer hij where
  toFun u := ⟨diagonalOneParameter u.toAdd.val u.toAdd.property.1 1,
    diagonal_mem_rootPairCentralizer hij _ _ u.toAdd.property.2 1⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    simp [diagonalOneParameter]
  map_mul' u v := by
    apply Subtype.ext
    exact diagonalOneParameter_add_weights _ _ u.toAdd.property.1 v.toAdd.property.1 1

lemma continuous_neutralDiagonalHom {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Continuous (neutralDiagonalHom hij) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  change Continuous (fun u : Multiplicative (neutralWeightSubgroup i j) =>
    Matrix.diagonal (fun r => Real.exp (u.toAdd.val r * 1)) a b)
  by_cases hab : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq, mul_one]
    exact Real.continuous_exp.comp ((continuous_apply a).comp
      (continuous_subtype_val.comp (show Continuous (fun u : Multiplicative
        (neutralWeightSubgroup i j) => u.toAdd) from continuous_id)))
  · simp only [Matrix.diagonal_apply_ne _ hab]
    exact continuous_const

/-- The opposite representation matches the right action on lattices. -/
def neutralDiagonalOppositeHom {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Multiplicative (neutralWeightSubgroup i j) →* MulOpposite (rootPairCentralizer hij) where
  toFun u := MulOpposite.op (neutralDiagonalHom hij u)
  map_one' := by simp
  map_mul' u v := by
    apply MulOpposite.unop_injective
    change neutralDiagonalHom hij (u * v) = neutralDiagonalHom hij v * neutralDiagonalHom hij u
    rw [← map_mul, mul_comm]

lemma continuous_neutralDiagonalOppositeHom {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Continuous (neutralDiagonalOppositeHom hij) :=
  MulOpposite.continuous_op.comp (continuous_neutralDiagonalHom hij)

end DukePrimeDegree

end

end OAI
