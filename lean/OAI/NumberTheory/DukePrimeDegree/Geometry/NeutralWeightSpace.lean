import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralDiagonal
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-!
# The finite-dimensional neutral weight space

Real scalar closure of the trace-zero neutral weights supplies a
locally compact abelian group with Haar measure. Its diagonal action
is the same neutral action used in the exceptional-return argument.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def neutralWeightSpace {n : ℕ} (i j : Fin n) : Submodule ℝ (Fin n → ℝ) where
  carrier := {ell | (∑ r, ell r) = 0 ∧ ell i = ell j}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, hai⟩ ⟨hb, hbi⟩
    constructor
    · simp only [Pi.add_apply, Finset.sum_add_distrib, ha, hb, add_zero]
    · simp only [Pi.add_apply, hai, hbi]
  smul_mem' := by
    rintro c a ⟨ha, hai⟩
    constructor
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ha, mul_zero]
    · simp only [Pi.smul_apply, hai]

def neutralSpaceDiagonal {n : ℕ} (i j : Fin n) :
    Multiplicative (neutralWeightSpace i j) →* G n where
  toFun u := diagonalOneParameter u.toAdd.val u.toAdd.property.1 1
  map_one' := by
    apply Subtype.ext
    simp [diagonalOneParameter]
  map_mul' u v :=
    diagonalOneParameter_add_weights _ _ u.toAdd.property.1 v.toAdd.property.1 1

theorem continuous_neutralSpaceDiagonal {n : ℕ} (i j : Fin n) :
    Continuous (neutralSpaceDiagonal i j) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  change Continuous (fun u : Multiplicative (neutralWeightSpace i j) =>
    Matrix.diagonal (fun r => Real.exp (u.toAdd.val r * 1)) a b)
  by_cases hab : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq, mul_one]
    exact Real.continuous_exp.comp ((continuous_apply a).comp
      (continuous_subtype_val.comp (show Continuous (fun u : Multiplicative
        (neutralWeightSpace i j) => u.toAdd) from continuous_id)))
  · simp only [Matrix.diagonal_apply_ne _ hab]
    exact continuous_const

end DukePrimeDegree

end

end OAI
