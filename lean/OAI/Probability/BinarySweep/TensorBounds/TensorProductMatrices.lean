import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.SignedCommutant

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I A B C : Type*} [Fintype I] [DecidableEq I]
 [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

def tensorMatrices (M : I → Matrix A B ℂ) : Matrix (I → A) (I → B) ℂ :=
  fun x y => ∏ i, M i (x i) (y i)

omit [Fintype A] [DecidableEq A] [DecidableEq B] [Fintype C] [DecidableEq C] in
lemma tensorMatrices_mul (M : I → Matrix A B ℂ) (N : I → Matrix B C ℂ) :
    tensorMatrices M * tensorMatrices N = tensorMatrices (fun i => M i * N i) := by
  ext x z
  simp only [Matrix.mul_apply,tensorMatrices,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b => M i (x i) b * N i b (z i))).symm

omit [DecidableEq I] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
lemma tensorMatrices_star (M : I → Matrix A B ℂ) :
    (tensorMatrices M).conjTranspose = tensorMatrices (fun i => (M i).conjTranspose) := by
  ext x y
  simp [tensorMatrices]

omit [DecidableEq I] [Fintype A] in
lemma tensorMatrices_one : tensorMatrices (fun _ : I => (1 : Matrix A A ℂ)) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y; simp [tensorMatrices]
  · have ⟨i,hi⟩ := Function.ne_iff.mp h
    simp only [tensorMatrices,Matrix.one_apply,ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

omit [DecidableEq A] in
lemma tensorMatrices_trace (M : I → Matrix A A ℂ) :
    (tensorMatrices M).trace = ∏ i, (M i).trace := by
  simp only [Matrix.trace,tensorMatrices,diag]
  exact (Fintype.prod_sum (fun i a => M i a a)).symm

lemma tensorMatrices_psd (M : I → Matrix A A ℂ) (hM : ∀ i, (M i).PosSemidef) :
    (tensorMatrices M).PosSemidef := by
  have hex (i : I) : ∃ X : Matrix A A ℂ, M i = X.conjTranspose * X := by
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hM i).nonneg
  choose X hX using hex
  have he : tensorMatrices M = (tensorMatrices X).conjTranspose * tensorMatrices X := by
    rw [tensorMatrices_star,tensorMatrices_mul]
    congr 1
    funext i
    exact hX i
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq I] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
lemma tensorMatrices_smul (a : I → ℂ) (M : I → Matrix A B ℂ) :
    tensorMatrices (fun i => a i • M i) = (∏ i, a i) • tensorMatrices M := by
  ext x y
  simp only [tensorMatrices,Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

omit [Fintype A] [DecidableEq A] in
lemma even_tensor_invariant (p : A → Bool) (M : Matrix A A ℂ)
    (hM : ∀ a b, p a ≠ p b → M a b = 0) :
    Invariant p (matrixTensorPower n M) := by
  intro g x y
  have hr : matrixTensorPower n M (x ∘ g) (y ∘ g) = matrixTensorPower n M x y := by
    exact Equiv.prod_comp g (fun i => M (x i) (y i))
  rw [hr]
  by_cases h : p ∘ x = p ∘ y
  · rw [h,signC_sq,one_mul]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    have hz : matrixTensorPower n M x y = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hM (x i) (y i) hi)
    simp [hz]

omit [DecidableEq A] in
lemma invariant_mulVec_commutes (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hM : Invariant p M) (g : Equiv.Perm (Fin n)) (v : (Fin n → A) → ℂ) :
    M.mulVec (act p g v) = act p g (M.mulVec v) := by
  funext x
  simp only [Matrix.mulVec,dotProduct,act_apply,Finset.mul_sum]
  conv_rhs => rw [← (wordReorder (A:=A) g).sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  have he := hM g x y
  dsimp only [wordReorder,Equiv.coe_fn_mk]
  rw [he]
  linear_combination -(signC (p ∘ y) g⁻¹ * M x y * v (y ∘ g)) * signC_sq (p ∘ x) g⁻¹

end BinaryCoordinateSweeps.Signed

end

end OAI
