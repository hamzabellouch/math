import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.SignedBlock
import OAI.Probability.BinarySweep.TensorBounds.SignedWhitening
import OAI.Probability.BinarySweep.Representations.IsotypicCentrality

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma actionMatrix_linear (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    (actionMatrix p g).toEuclideanLin=hilbertTensorRep p n g := by
  ext v x
  change ((LinearMap.toMatrix' (act p g)).mulVec (coeffEquiv A n v)) x = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

lemma invariant_matrix_commutes (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hM : Invariant p M) (g : Equiv.Perm (Fin n)) :
    M*actionMatrix p g=actionMatrix p g*M := by
  apply Matrix.toEuclideanLin.injective
  simp only [Matrix.toLpLin_mul_same,actionMatrix_linear]
  apply LinearMap.ext
  intro v
  apply (coeffEquiv A n).injective
  exact invariant_mulVec_commutes p M hM g (coeffEquiv A n v)

omit [FiniteDimensional ℂ V] in
lemma typeProjection_commutes_action (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (g : Equiv.Perm (Fin n)) :
    isotypicProjection p ρ*actionMatrix p g=actionMatrix p g*isotypicProjection p ρ :=
  invariant_matrix_commutes p _ (isotypicProjection_invariant p ρ) g

omit [FiniteDimensional ℂ V] in
lemma typeProjection_central (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hc : ∀g, M*actionMatrix p g=actionMatrix p g*M) :
    M*isotypicProjection p ρ=isotypicProjection p ρ*M := by
  have hh (g : Equiv.Perm (Fin n)) (v : TensorSpace A n) :
      M.toEuclideanLin (hilbertTensorRep p n g v)=hilbertTensorRep p n g (M.toEuclideanLin v) := by
    have h := congrArg (fun Q => Q.toEuclideanLin v) (hc g)
    simpa only [Matrix.toLpLin_mul_same,LinearMap.comp_apply,actionMatrix_linear] using h
  have h := isotypicProjection_central ρ (hilbertTensorRep p n)
    (hilbertTensorRep_unitary p) M hh
  simpa only [hilbert_isotypic_eq,isotypicProjection] using h

end BinaryCoordinateSweeps.Signed

end

end OAI
