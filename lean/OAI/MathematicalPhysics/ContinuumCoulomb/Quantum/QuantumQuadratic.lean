import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryWitness
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

/-! Finite matrix quadratic forms used by the explicit history Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaQuadratic {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (u : ι → ℂ) : ℝ :=
  (star u ⬝ᵥ M.mulVec u).re

theorem qmaQuadratic_add {ι : Type*} [Fintype ι]
    (M N : Matrix ι ι ℂ) (u : ι → ℂ) :
    qmaQuadratic (M+N) u = qmaQuadratic M u+qmaQuadratic N u := by
  simp [qmaQuadratic,Matrix.add_mulVec,dotProduct_add]

theorem qmaQuadratic_smul {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (a : ℝ) (u : ι → ℂ) :
    qmaQuadratic ((a:ℂ) • M) u = a*qmaQuadratic M u := by
  simp [qmaQuadratic,Matrix.smul_mulVec,dotProduct_smul,Complex.mul_re]

theorem qmaQuadratic_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : Matrix κ ι ℂ) (u : ι → ℂ) :
    qmaQuadratic (D.conjTranspose*D) u = ∑ r, Complex.normSq (D.mulVec u r) := by
  have he : star u ⬝ᵥ (D.conjTranspose*D).mulVec u =
      star (D.mulVec u) ⬝ᵥ D.mulVec u := by
    rw [Matrix.star_mulVec,←Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec]
  rw [qmaQuadratic,he]
  simp only [dotProduct,Complex.re_sum,Pi.star_apply]
  apply Finset.sum_congr rfl
  intro r _
  simp [Complex.mul_re,Complex.normSq_apply]

theorem qmaQuadratic_diagonal_mask {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) (u : ι → ℂ) :
    qmaQuadratic (Matrix.diagonal (fun i => if p i then (1:ℂ) else 0)) u =
      ∑ i, if p i then Complex.normSq (u i) else 0 := by
  classical
  simp only [qmaQuadratic,dotProduct,Matrix.mulVec_diagonal,Complex.re_sum,Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p i
  · simp [hi,Complex.mul_re,Complex.normSq_apply]
  · simp [hi]

end ContinuumCoulomb

end

end OAI
