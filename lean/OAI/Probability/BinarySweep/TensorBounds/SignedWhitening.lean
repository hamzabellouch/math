import Mathlib
import OAI.Probability.BinarySweep.Representations.MatrixIsotypicWhitening
import OAI.Probability.BinarySweep.Representations.IsotypicDensity

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Irrep Density Representation

variable {A V : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def hilbertTensorRep (p : A → Bool) (n : ℕ) :
    Representation ℂ (Equiv.Perm (Fin n)) (TensorSpace A n) :=
  conjugateRep (tensorRep p n) (coeffEquiv A n).symm

omit [DecidableEq A] in
lemma hilbertTensorRep_apply (p : A → Bool) (g : Equiv.Perm (Fin n)) (v : TensorSpace A n) :
    hilbertTensorRep p n g v = actHilbert p g v := rfl

omit [DecidableEq A] in
lemma hilbertTensorRep_unitary (p : A → Bool) (g : Equiv.Perm (Fin n)) (v : TensorSpace A n) :
    ‖hilbertTensorRep p n g v‖ = ‖v‖ := (actionIsometry p g).norm_map v

omit [FiniteDimensional ℂ V] [DecidableEq A] in
lemma hilbert_isotypic_eq (p : A → Bool) (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    isotypicSpan ρ (hilbertTensorRep p n) = hilbertSubspace (isotypicSpan ρ (tensorRep p n)) := by
  exact (map_isotypic_equiv ρ (tensorRep p n) (hilbertTensorRep p n)
    (conjugateEquiv (tensorRep p n) (coeffEquiv A n).symm)).symm

lemma even_tensor_hilbert_commutes (p : A → Bool) (M : Matrix A A ℂ)
    (hM : ∀ a b, p a ≠ p b → M a b = 0) (g : Equiv.Perm (Fin n)) (v : TensorSpace A n) :
    (matrixTensorPower n M).toEuclideanLin (hilbertTensorRep p n g v) =
      hilbertTensorRep p n g ((matrixTensorPower n M).toEuclideanLin v) := by
  apply (coeffEquiv A n).injective
  exact invariant_mulVec_commutes p (matrixTensorPower n M) (even_tensor_invariant p M hM) g
    (coeffEquiv A n v)

omit [FiniteDimensional ℂ V] in
theorem signed_tensor_whitening (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible]
    (M B C : Matrix A A ℂ) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hBB : B*B=M) (hBC : B*C=1) (ht : M.trace=1)
    (heM : ∀ a b, p a ≠ p b → M a b = 0)
    (heC : ∀ a b, p a ≠ p b → C a b = 0) :
    ((matrixTensorPower n C).conjTranspose * matrixTensorPower n C -
      (Module.finrank ℂ V : ℂ) • isotypicProjection p ρ).PosSemidef := by
  have hpow (N : Matrix A A ℂ) : matrixTensorPower n N = tensorMatrices (fun _ : Fin n => N) := rfl
  have hBA : matrixTensorPower n B * matrixTensorPower n C = 1 := by
    rw [hpow,hpow,tensorMatrices_mul]
    simpa only [hBC] using (tensorMatrices_one (I:=Fin n) (A:=A))
  have hBT : (matrixTensorPower n B).conjTranspose * matrixTensorPower n B =
      matrixTensorPower n M := by
    rw [hpow,hpow,tensorMatrices_star,tensorMatrices_mul]
    simp only [hB.isHermitian.eq,hBB]
  have hCt : (matrixTensorPower n C).PosSemidef := by
    rw [hpow]; exact tensorMatrices_psd _ (fun _ => hC)
  have h := matrix_whitening_positive ρ (hilbertTensorRep p n)
    (matrixTensorPower n B) (matrixTensorPower n C) hCt.isHermitian
    (even_tensor_hilbert_commutes p C heC) hBA (by
      rw [hBT]; exact even_tensor_hilbert_commutes p M heM)
    (hilbertTensorRep_unitary p) (by rw [hBT,hpow,tensorMatrices_trace]; simp [ht])
  simpa only [hilbert_isotypic_eq,isotypicProjection] using h

end BinaryCoordinateSweeps.Signed

end

end OAI
