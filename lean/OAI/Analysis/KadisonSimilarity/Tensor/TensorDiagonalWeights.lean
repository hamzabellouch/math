import OAI.Analysis.KadisonSimilarity.Tensor.TensorMatrixAlgebra
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace OAI

/-! Diagonal unitary phases separate the multiplicity weights of a finite
tensor power. This is the weight calculation in the Schur--Weyl argument. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- The multiplicity of a label in an elementary tensor. -/
def tensorLabelCount (f : ι → α) (a : α) : ℕ := Fintype.card {i // f i = a}

omit [DecidableEq ι] [Fintype α] in
theorem tensorLabelCount_le (f : ι → α) (a : α) :
    tensorLabelCount f a ≤ Fintype.card ι := Fintype.card_subtype_le _

omit [DecidableEq ι] in
theorem prod_labels_eq (f : ι → α) (d : α → ℂ) :
    (∏ i, d (f i)) = ∏ a, d a ^ tensorLabelCount f a := by
  rw [← Fintype.prod_fiberwise' f d]
  simp only [Finset.prod_const, Finset.card_univ, tensorLabelCount]

omit [DecidableEq ι] [Fintype α] in
theorem tupleTensorMatrix_diagonal (d : α → ℂ) :
    tupleTensorMatrix (fun _ : ι => Matrix.diagonal d) =
      Matrix.diagonal (fun f : ι → α => ∏ i, d (f i)) := by
  ext f g
  simp only [tupleTensorMatrix_apply, Matrix.diagonal_apply, Fintype.prod_ite_zero]
  congr 1
  exact propext funext_iff.symm

/-- A scalar diagonal whose entries lie on the unit circle. -/
def tensorDiagonalUnitary (d : α → unitary ℂ) : Matrix.unitaryGroup α ℂ :=
  ⟨Matrix.diagonal (fun a => (d a : ℂ)), by
    constructor <;> ext i j <;> by_cases hij : i = j
    · subst j
      simpa only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul, Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.one_apply_eq,
        Complex.star_def] using (d i).property.1
    · simp [Matrix.star_eq_conjTranspose, hij]
    · subst j
      simpa only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.mul_diagonal, Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.one_apply_eq,
        Complex.star_def] using (d i).property.2
    · simp [Matrix.star_eq_conjTranspose, hij]⟩

private def tensorRoot (n : ℕ) : unitary ℂ :=
  let z := Complex.exp (2 * Real.pi * Complex.I / n)
  have hn : ‖z‖ = 1 := by
    dsimp [z]
    have he : (2 * (Real.pi : ℂ) * Complex.I / n) =
        ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he]
    exact Complex.norm_exp_ofReal_mul_I _
  have hz : star z * z = 1 := by
    change starRingEnd ℂ z * z = 1
    rw [Complex.conj_mul', hn]
    norm_num
  ⟨z, hz, by rw [mul_comm]; exact hz⟩

omit [DecidableEq ι] in
private theorem phase_product (f : ι → α) (a : α) (z : ℂ) :
    (∏ i, if f i = a then z else 1) = z ^ tensorLabelCount f a := by
  rw [prod_labels_eq f (fun b => if b = a then z else 1)]
  simp only [ite_pow, one_pow]
  simp

/-- Distinct label multiplicities cannot occur in the support of an operator
commuting with all tensor powers of unitaries. -/
theorem tensor_commutant_entry_zero_of_weight_ne
    (C : Matrix (ι → α) (ι → α) ℂ)
    (hC : ∀ u : Matrix.unitaryGroup α ℂ,
      C * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) =
        tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * C)
    (f g : ι → α) (a : α) (hne : tensorLabelCount f a ≠ tensorLabelCount g a) :
    C f g = 0 := by
  let n := Fintype.card ι + 1
  let z := tensorRoot n
  let d : α → unitary ℂ := fun b => if b = a then z else 1
  have hp : IsPrimitiveRoot (z : ℂ) n := Complex.isPrimitiveRoot_exp n (by dsimp [n]; omega)
  have hfg := congrArg (fun M : Matrix (ι → α) (ι → α) ℂ => M f g)
    (hC (tensorDiagonalUnitary d))
  change (C * tupleTensorMatrix (fun _ : ι => Matrix.diagonal (fun b => (d b : ℂ)))) f g =
    (tupleTensorMatrix (fun _ : ι => Matrix.diagonal (fun b => (d b : ℂ))) * C) f g at hfg
  rw [tupleTensorMatrix_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at hfg
  have hd (r : ι → α) : (∏ i, (d (r i) : ℂ)) = (z : ℂ) ^ tensorLabelCount r a := by
    simpa only [d, apply_ite, OneMemClass.coe_one] using phase_product r a (z : ℂ)
  rw [hd, hd, mul_comm _ (C f g)] at hfg
  by_contra hc
  have heq := mul_left_cancel₀ hc hfg
  exact hne (hp.pow_inj (by have := tensorLabelCount_le g a; dsimp [n]; omega)
    (by have := tensorLabelCount_le f a; dsimp [n]; omega) heq).symm

/-- Every complex diagonal commutes with the tensor commutant; the unit-circle
condition on the testing diagonals has disappeared. -/
theorem tensor_commutant_commutes_diagonal
    (C : Matrix (ι → α) (ι → α) ℂ)
    (hC : ∀ u : Matrix.unitaryGroup α ℂ,
      C * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) =
        tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * C)
    (d : α → ℂ) :
    C * tupleTensorMatrix (fun _ : ι => Matrix.diagonal d) =
      tupleTensorMatrix (fun _ : ι => Matrix.diagonal d) * C := by
  rw [tupleTensorMatrix_diagonal]
  ext f g
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : ∀ a, tensorLabelCount f a = tensorLabelCount g a
  · rw [prod_labels_eq f, prod_labels_eq g]
    simp_rw [h]
    exact mul_comm _ _
  · obtain ⟨a, ha⟩ := not_forall.mp h
    rw [tensor_commutant_entry_zero_of_weight_ne C hC f g a ha]
    simp

end KadisonSimilarity

end

end OAI
