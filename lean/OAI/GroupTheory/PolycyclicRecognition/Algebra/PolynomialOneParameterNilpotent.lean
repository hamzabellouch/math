import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlgebraOneParameter
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Matrix.Normed
import Mathlib.RingTheory.Nilpotent.Basic

namespace OAI

/-! # Polynomial matrix one-parameter groups have nilpotent derivative

Successive derivatives are left multiplication by successive powers of the
initial derivative. A polynomial degree bound therefore forces one power to
vanish. This argument uses neither eigenvalues nor triangularization.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

def matrixEntryLinear (i j : I) : Matrix I I ℝ →L[ℝ] ℝ :=
  ({ toFun := fun A => A i j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Matrix I I ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

omit [DecidableEq I] in
theorem matrixEntryLinear_apply (i j : I) (A : Matrix I I ℝ) :
    matrixEntryLinear i j A = A i j := rfl

theorem polynomial_oneParameter_derivatives
    {f : ℝ → Matrix I I ℝ} {A : Matrix I I ℝ}
    (hadd : ∀ s t, f (s + t) = f s * f t) (hzero : HasDerivAt f A 0)
    (p : I → I → Polynomial ℝ) (hp : ∀ i j t, (p i j).eval t = f t i j)
    (k : ℕ) (i j : I) (t : ℝ) :
    ((Polynomial.derivative^[k]) (p i j)).eval t = (A ^ k * f t) i j := by
  induction k generalizing t with
  | zero => simpa using hp i j t
  | succ k hk =>
    have h₁ := (((Polynomial.derivative^[k]) (p i j)).hasDerivAt t)
    have heq : (fun s => ((Polynomial.derivative^[k]) (p i j)).eval s) =
        (fun s => (A ^ k * f s) i j) := funext hk
    rw [heq] at h₁
    have h₂ := (matrixEntryLinear i j).hasFDerivAt.comp_hasDerivAt t
      ((oneParameter_hasDerivAt hadd hzero t).const_mul (A ^ k))
    change HasDerivAt (fun s => (A ^ k * f s) i j) ((A ^ k * (A * f t)) i j) t at h₂
    have h := h₁.unique h₂
    simpa only [Function.iterate_succ_apply', matrixEntryLinear_apply,
      pow_succ, mul_assoc] using h

theorem isNilpotent_of_polynomial_oneParameter
    {f : ℝ → Matrix I I ℝ} {A : Matrix I I ℝ}
    (hf0 : f 0 = 1) (hadd : ∀ s t, f (s + t) = f s * f t)
    (hzero : HasDerivAt f A 0)
    (hpoly : ∀ i j, ∃ p : Polynomial ℝ, ∀ t, p.eval t = f t i j) :
    IsNilpotent A := by
  choose p hp using hpoly
  let d := (Finset.univ : Finset (I × I)).sup (fun ij => (p ij.1 ij.2).natDegree)
  refine ⟨d + 1, ?_⟩
  ext i j
  have hi : (p i j).natDegree < d + 1 := by
    have hle : (p i j).natDegree ≤ d := Finset.le_sup (f := fun ij : I × I =>
      (p ij.1 ij.2).natDegree) (Finset.mem_univ (i, j))
    exact Nat.lt_succ_of_le hle
  have h := polynomial_oneParameter_derivatives hadd hzero p hp (d + 1) i j 0
  rw [Polynomial.iterate_derivative_eq_zero hi, Polynomial.eval_zero, hf0, mul_one] at h
  exact h.symm

end PolycyclicRecognition

end

end OAI
