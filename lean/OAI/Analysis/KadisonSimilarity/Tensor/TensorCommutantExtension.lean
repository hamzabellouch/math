import OAI.Analysis.KadisonSimilarity.Tensor.TensorDiagonalWeights
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Complex.Module

namespace OAI

/-! Extending a tensor commutation identity from unitary matrices to all
matrices. Diagonal weights, Hermitian diagonalization and a polynomial
identity suffice; no decomposition of a general matrix is assumed. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- Commutation with unitary tensor powers implies commutation with every
Hermitian tensor power. -/
theorem tensor_commutant_commutes_hermitian
    (C : Matrix (ι → α) (ι → α) ℂ)
    (hC : ∀ u : Matrix.unitaryGroup α ℂ,
      C * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) =
        tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * C)
    (a : Matrix α α ℂ) (ha : a.IsHermitian) :
    C * tupleTensorMatrix (fun _ : ι => a) =
      tupleTensorMatrix (fun _ : ι => a) * C := by
  let u := ha.eigenvectorUnitary
  let d : Matrix α α ℂ := Matrix.diagonal (RCLike.ofReal ∘ ha.eigenvalues : α → ℂ)
  have ha' : a = (u : Matrix α α ℂ) * d * star (u : Matrix α α ℂ) := by
    simpa only [u, d, Unitary.conjStarAlgAut_apply, Unitary.coe_star] using ha.spectral_theorem
  rw [ha', tupleTensorMatrix_mul, tupleTensorMatrix_mul]
  have hu := hC u
  have hs := hC (star u)
  have hd := tensor_commutant_commutes_diagonal C hC (RCLike.ofReal ∘ ha.eigenvalues : α → ℂ)
  change C * (tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) *
      tupleTensorMatrix (fun _ : ι => d) *
      tupleTensorMatrix (fun _ : ι => star (u : Matrix α α ℂ))) = _
  calc
    _ = (C * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ))) *
        tupleTensorMatrix (fun _ : ι => d) *
        tupleTensorMatrix (fun _ : ι => star (u : Matrix α α ℂ)) := by
      simp only [Matrix.mul_assoc]
    _ = (tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * C) *
        tupleTensorMatrix (fun _ : ι => d) *
        tupleTensorMatrix (fun _ : ι => star (u : Matrix α α ℂ)) := by rw [hu]
    _ = tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) *
        (tupleTensorMatrix (fun _ : ι => d) * C) *
        tupleTensorMatrix (fun _ : ι => star (u : Matrix α α ℂ)) := by
      rw [Matrix.mul_assoc _ C, hd]
    _ = _ := by
      simpa only [← Matrix.mul_assoc, Unitary.coe_star] using congrArg
        (fun X => tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) *
          tupleTensorMatrix (fun _ : ι => d) * X) hs

private def tensorCommutatorPolynomial (C : Matrix (ι → α) (ι → α) ℂ)
    (a b : Matrix α α ℂ) (f g : ι → α) : Polynomial ℂ :=
  (∑ h : ι → α, Polynomial.C (C f h) *
    ∏ i, (Polynomial.C (a (h i) (g i)) + Polynomial.X * Polynomial.C (b (h i) (g i)))) -
  ∑ h : ι → α, (∏ i, (Polynomial.C (a (f i) (h i)) +
    Polynomial.X * Polynomial.C (b (f i) (h i)))) * Polynomial.C (C h g)

omit [DecidableEq α] in
private theorem tensorCommutatorPolynomial_eval (C : Matrix (ι → α) (ι → α) ℂ)
    (a b : Matrix α α ℂ) (f g : ι → α) (z : ℂ) :
    (tensorCommutatorPolynomial C a b f g).eval z =
      (C * tupleTensorMatrix (fun _ : ι => a + z • b)) f g -
        (tupleTensorMatrix (fun _ : ι => a + z • b) * C) f g := by
  simp only [tensorCommutatorPolynomial, Polynomial.eval_sub, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X, Matrix.mul_apply, tupleTensorMatrix_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]

omit [DecidableEq α] in
/-- A polynomial commutation identity on a real line also holds on its
complexification. -/
theorem tensor_commutes_complex_line
    (C : Matrix (ι → α) (ι → α) ℂ) (a b : Matrix α α ℂ)
    (h : ∀ t : ℝ,
      C * tupleTensorMatrix (fun _ : ι => a + (t : ℂ) • b) =
        tupleTensorMatrix (fun _ : ι => a + (t : ℂ) • b) * C)
    (z : ℂ) :
    C * tupleTensorMatrix (fun _ : ι => a + z • b) =
      tupleTensorMatrix (fun _ : ι => a + z • b) * C := by
  ext f g
  have hzero : tensorCommutatorPolynomial C a b f g = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
    rintro _ ⟨t, rfl⟩
    change (tensorCommutatorPolynomial C a b f g).eval (t : ℂ) = 0
    rw [tensorCommutatorPolynomial_eval, h t, sub_self]
  have hz := congrArg (Polynomial.eval z) hzero
  simpa only [tensorCommutatorPolynomial_eval, Polynomial.eval_zero, sub_eq_zero] using hz

/-- The exact unitary-to-all-matrices extension needed for finite tensor
Schur--Weyl spanning. -/
theorem tensor_commutant_commutes_matrix
    (C : Matrix (ι → α) (ι → α) ℂ)
    (hC : ∀ u : Matrix.unitaryGroup α ℂ,
      C * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) =
        tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * C)
    (a : Matrix α α ℂ) :
    C * tupleTensorMatrix (fun _ : ι => a) =
      tupleTensorMatrix (fun _ : ι => a) * C := by
  have hre : (realPart a : Matrix α α ℂ).IsHermitian := (realPart a).property
  have him : (imaginaryPart a : Matrix α α ℂ).IsHermitian := (imaginaryPart a).property
  have hline (t : ℝ) := tensor_commutant_commutes_hermitian C hC
    ((realPart a : Matrix α α ℂ) + (t : ℂ) • (imaginaryPart a : Matrix α α ℂ))
    (hre.add (him.smul (by change star (t : ℂ) = (t : ℂ); simp)))
  have he := tensor_commutes_complex_line C (realPart a) (imaginaryPart a) hline Complex.I
  simpa only [realPart_add_I_smul_imaginaryPart] using he

end KadisonSimilarity

end

end OAI
