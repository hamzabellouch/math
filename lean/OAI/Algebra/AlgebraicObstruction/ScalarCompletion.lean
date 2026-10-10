import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.SeriesJets
import OAI.Algebra.AlgebraicObstruction.AdicFunctor

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionScalar
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

def quotientEquiv (I : Ideal R) (n : ℕ) :
    (S ⧸ (I ^ n • ⊤ : Submodule R S)) ≃ₗ[R]
      (S ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Ideal S)) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
    simp)).trans (Submodule.Quotient.restrictScalarsEquiv R _)

@[simp] lemma quotientEquiv_mk (I : Ideal R) (n : ℕ) (s : S) :
    quotientEquiv I n (Submodule.Quotient.mk s) = Submodule.Quotient.mk s := by
  simp only [quotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    Submodule.Quotient.restrictScalarsEquiv_mk]

@[simp] lemma quotientEquiv_symm_mk (I : Ideal R) (n : ℕ) (s : S) :
    (quotientEquiv I n).symm (Submodule.Quotient.mk s) = Submodule.Quotient.mk s := by
  apply (quotientEquiv I n).injective
  rw [LinearEquiv.apply_symm_apply, quotientEquiv_mk]

lemma quotientEquiv_transition (I : Ideal R) {m n : ℕ} (h : m ≤ n)
    (x : S ⧸ (I ^ n • ⊤ : Submodule R S)) :
    AdicCompletion.transitionMap (I.map (algebraMap R S)) S h
      (quotientEquiv I n x) =
    quotientEquiv I m (AdicCompletion.transitionMap I S h x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ s =>
      rw [quotientEquiv_mk]
      exact (quotientEquiv_mk I m s).symm

lemma quotientEquiv_symm_transition (I : Ideal R) {m n : ℕ} (h : m ≤ n)
    (x : S ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Ideal S)) :
    AdicCompletion.transitionMap I S h ((quotientEquiv I n).symm x) =
    (quotientEquiv I m).symm
      (AdicCompletion.transitionMap (I.map (algebraMap R S)) S h x) := by
  apply (quotientEquiv I m).injective
  rw [← quotientEquiv_transition, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

def equiv (I : Ideal R) :
    AdicCompletion I S ≃ₗ[R] AdicCompletion (I.map (algebraMap R S)) S where
  toFun x := ⟨fun n ↦ quotientEquiv I n (x.val n), fun h ↦ by
    rw [quotientEquiv_transition, x.property h]⟩
  invFun x := ⟨fun n ↦ (quotientEquiv I n).symm (x.val n), fun h ↦ by
    rw [quotientEquiv_symm_transition, x.property h]⟩
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (quotientEquiv I n).symm_apply_apply _
  right_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (quotientEquiv I n).apply_symm_apply _
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    exact map_add (quotientEquiv I n) _ _
  map_smul' r x := by
    apply AdicCompletion.ext
    intro n
    exact (quotientEquiv I n).map_smul r _

@[simp] theorem equiv_of (I : Ideal R) (s : S) :
    equiv I (AdicCompletion.of I S s) =
      AdicCompletion.of (I.map (algebraMap R S)) S s := by
  apply AdicCompletion.ext
  intro n
  exact quotientEquiv_mk I n s

def tensorEquiv [IsNoetherianRing R] [Module.Finite R S] (I : Ideal R) :
    TensorProduct R (AdicCompletion I R) S ≃ₗ[R]
      AdicCompletion (I.map (algebraMap R S)) S :=
  ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I S).restrictScalars R).trans
    (equiv I)

@[simp] theorem tensorEquiv_one_tmul [IsNoetherianRing R] [Module.Finite R S]
    (I : Ideal R) (s : S) :
    tensorEquiv I (1 ⊗ₜ[R] s) = AdicCompletion.of (I.map (algebraMap R S)) S s := by
  change equiv I (AdicCompletion.ofTensorProduct I S (1 ⊗ₜ[R] s)) = _
  rw [AdicCompletion.ofTensorProduct_tmul, one_smul, equiv_of]

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionScalar

end

end OAI
