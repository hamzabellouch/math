import OAI.Analysis.KLS.Model
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

namespace OAI

noncomputable section
open Set Matrix
open scoped BigOperators ContDiff

namespace LeanBlast.KLS

def standardBasisVector {n : ℕ} (i : Fin n) : Space n :=
  EuclideanSpace.basisFun (Fin n) ℝ i

def partialDerivative {n : ℕ} (f : Space n → ℝ) (i : Fin n) (x : Space n) : ℝ :=
  fderiv ℝ f x (standardBasisVector i)

def hessianMatrix {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ f) x (standardBasisVector i) (standardBasisVector j)

def hessianSlice {n : ℕ} (f : Space n → ℝ) (x : Space n) (i : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fderiv ℝ (hessianMatrix f) x (standardBasisVector i)

def matrixHSNormSq {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

def steinGenerator {n : ℕ} (ψ V g : Space n → ℝ) (x : Space n) : ℝ :=
  Matrix.trace ((hessianMatrix ψ x)⁻¹ * hessianMatrix g x) -
    inner ℝ (gradient V (gradient ψ x)) (gradient g x)

def steinGamma {n : ℕ} (ψ g h : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ a, ∑ b, gradient g x a * (hessianMatrix ψ x)⁻¹ a b * gradient h x b

def steinQ {n : ℕ} (ψ : Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  Matrix.trace ((hessianMatrix ψ x)⁻¹ * hessianSlice ψ x i *
    (hessianMatrix ψ x)⁻¹ * hessianSlice ψ x j)

def steinHessianEnergy {n : ℕ} (ψ : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, steinGamma ψ (fun y => hessianMatrix ψ y i j)
    (fun y => hessianMatrix ψ y i j) x

theorem hessianMatrix_isSymm {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) : (hessianMatrix f x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq _ _

theorem matrixHSNormSq_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) : 0 ≤ matrixHSNormSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem matrixHSNormSq_eq_trace_sq {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) : matrixHSNormSq A = Matrix.trace (A * A) := by
  simp only [matrixHSNormSq, Matrix.trace, pow_two]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change A i j * A i j = A i j * A j i
  rw [hA.apply i j]

end LeanBlast.KLS

end

end OAI
