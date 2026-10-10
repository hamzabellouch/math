import OAI.Analysis.FreeEntropy.GUEOperatorTail

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate Classical
open Finset
namespace FiniteEntropySeparation
 variable {α : Type u1} {n d : ℕ}
 def jointMatrix (A : α → Matrix (Fin d) (Fin d) ℂ) (x : MatrixIndex n d → ℝ) : α ⊕ Fin n → Matrix (Fin d) (Fin d) ℂ := Sum.elim A (gueMatrix x)
 def matrixTraceWord (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List α) : ℂ := (d:ℂ)⁻¹ * Matrix.trace (matrixWord A w)
 def noiseDirection (q : MatrixIndex n d) : α ⊕ Fin n → Matrix (Fin d) (Fin d) ℂ := fun a =>
   if a=Sum.inr q.1 then ((Real.sqrt d : ℂ)⁻¹) • hermitianBasis q.2.1 q.2.2 else 0
 theorem jointMatrix_polynomial (A : α → Matrix (Fin d) (Fin d) ℂ) (a : α ⊕ Fin n) :
    IsMatrixPolynomial (fun x : MatrixIndex n d → ℝ => jointMatrix A x a) := by
  cases a with
  | inl a => exact IsMatrixPolynomial.const (A a)
  | inr i => exact (show IsMatrixPolynomial (fun x : MatrixIndex n d → ℝ => coordinateMatrix x i) from fun j k => coordinateMatrix_polynomial i j k).smul _
 theorem jointMatrix_hasDeriv (A : α → Matrix (Fin d) (Fin d) ℂ) (x : MatrixIndex n d → ℝ) (q : MatrixIndex n d)
    (a : α ⊕ Fin n) (j k : Fin d) :
    HasDerivAt (fun t => jointMatrix A (Function.update x q t) a j k) (noiseDirection (α := α) q a j k) (x q) := by
  classical
  cases a with
  | inl a => simpa [jointMatrix, noiseDirection] using hasDerivAt_const (x q) (A a j k)
  | inr i =>
    have hh := (coordinateMatrix_hasDeriv x q i j k).const_mul ((Real.sqrt d:ℂ)⁻¹)
    by_cases h : q.1=i
    · simpa [jointMatrix, gueMatrix, noiseDirection, h] using hh
    · simpa [jointMatrix, gueMatrix, noiseDirection, h, Ne.symm h] using hh
 theorem matrixTraceWord_polynomial (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List (α ⊕ Fin n)) :
    IsComplexPolynomial (fun x : MatrixIndex n d → ℝ => matrixTraceWord (jointMatrix A x) w) :=
  ((IsMatrixPolynomial.word (jointMatrix_polynomial A) w).trace).const_mul _
 theorem matrixTraceWord_derivative (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List (α ⊕ Fin n))
    (q : MatrixIndex n d) (x : MatrixIndex n d → ℝ) :
    complexCoordinateDerivative (fun y => matrixTraceWord (jointMatrix A y) w) q x =
      ((d:ℂ)⁻¹ * (Real.sqrt d:ℂ)⁻¹) * ∑ r : Fin w.length,
        if w[r.val]=Sum.inr q.1 then Matrix.trace (hermitianBasis q.2.1 q.2.2 * cyclicMatrixWord (jointMatrix A x) w r) else 0 := by
  classical
  have hd := (hasDerivAt_matrixWord_trace (jointMatrix_hasDeriv A x q) w).const_mul ((d:ℂ)⁻¹)
  have he := hd.deriv
  change complexCoordinateDerivative (fun y => matrixTraceWord (jointMatrix A y) w) q x = _ at he
  simp only [Function.update_eq_self] at he
  rw [he, matrixWordVariation_trace]
  simp only [noiseDirection, cyclicMatrixWord]
  rw [mul_assoc]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro r _
  split_ifs <;> simp [Matrix.trace_smul]
end FiniteEntropySeparation

end

end OAI
