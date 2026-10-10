import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.TaylorShift
import OAI.Algebra.AlgebraicObstruction.ScalarCompletion

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
namespace TaylorShift
universe u
variable {K A α : Type u} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]
  [Algebra.FormallySmooth (MvPolynomial α K) A]

noncomputable def completionAlgEquiv (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) :
    letI := (taylor (K := K) (α := α) I q hq).toAlgebra
    letI : Module A (Target (α := α) I q) :=
      (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
    AdicCompletion (J.map (taylor (K := K) (α := α) I q hq)) (Target (α := α) I q) ≃ₐ[A]
      AdicCompletion (J.map (coefficient (α := α) I q)) (Target (α := α) I q) := by
  letI := (taylor (K := K) (α := α) I q hq).toAlgebra
  letI : Module A (Target (α := α) I q) :=
    (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
  exact { completionEquiv (K := K) I J q hq with
    commutes' := fun a ↦ completionEquiv_of I J q hq
      (taylor (K := K) (α := α) I q hq a) }

noncomputable def tensorCompletionEquiv [IsNoetherianRing A] [Finite α]
    (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) :
    letI := (taylor (K := K) (α := α) I q hq).toAlgebra
    letI : Module A (Target (α := α) I q) :=
      (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
    TensorProduct A (AdicCompletion J A) (Target (α := α) I q) ≃ₗ[A]
      AdicCompletion (J.map (coefficient (α := α) I q)) (Target (α := α) I q) := by
  letI := (taylor (K := K) (α := α) I q hq).toAlgebra
  letI : Module A (Target (α := α) I q) :=
    (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
  have : Module.Finite A (Target (α := α) I q) := taylor_finite (K := K) (α := α) I q hq
  exact (CompletionScalar.tensorEquiv J).trans
    (completionAlgEquiv (K := K) I J q hq).toLinearEquiv

@[simp] theorem tensorCompletionEquiv_one_tmul [IsNoetherianRing A] [Finite α]
    (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) (t : Target (α := α) I q) :
    letI := (taylor (K := K) (α := α) I q hq).toAlgebra
    letI : Module A (Target (α := α) I q) :=
      (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
    tensorCompletionEquiv (K := K) I J q hq (1 ⊗ₜ[A] t) =
      AdicCompletion.of (J.map (coefficient (α := α) I q)) _ t := by
  let := (taylor (K := K) (α := α) I q hq).toAlgebra
  let : Module A (Target (α := α) I q) :=
    (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
  have : Module.Finite A (Target (α := α) I q) := taylor_finite (K := K) (α := α) I q hq
  simp only [tensorCompletionEquiv, LinearEquiv.trans_apply,
    CompletionScalar.tensorEquiv_one_tmul]
  exact completionEquiv_of I J q hq t

end TaylorShift
end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget
open TensorProduct
variable {R S C α : Type*} [CommRing R] [CommRing S] [CommRing C]
  [Algebra R S] [Algebra R C]

lemma polynomialTensor_X (i : α) :
    (MvPolynomial.rTensorAlgEquiv (R := R) (S := S))
      (1 ⊗ₜ[R] (MvPolynomial.X i : MvPolynomial α C)) = MvPolynomial.X i := by
  classical
  ext e
  rw [MvPolynomial.coeff_rTensorAlgEquiv_tmul]
  simp only [MvPolynomial.coeff_X]
  split_ifs
  · rfl
  · exact TensorProduct.tmul_zero _ _

lemma polynomialTensor_ideal (q : ℕ) :
    ((variablesIdeal C α ^ q).map
      (Algebra.TensorProduct.includeRight : MvPolynomial α C →ₐ[R]
        S ⊗[R] MvPolynomial α C)).map
      (MvPolynomial.rTensorAlgEquiv (R := R) (S := S)).toRingHom =
      variablesIdeal (S ⊗[R] C) α ^ q := by
  rw [Ideal.map_pow, Ideal.map_pow]
  congr 1
  change ((variablesIdeal C α).map
    (Algebra.TensorProduct.includeRight : MvPolynomial α C →ₐ[R]
      S ⊗[R] MvPolynomial α C).toRingHom).map _ = _
  rw [Ideal.map_map]
  change (Ideal.span (Set.range (MvPolynomial.X : α → MvPolynomial α C))).map _ = _
  rw [Ideal.map_span, ← Set.range_comp]
  have hh : (MvPolynomial.rTensorAlgEquiv (R := R) (S := S)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : MvPolynomial α C →ₐ[R]
        S ⊗[R] MvPolynomial α C).toRingHom ∘ MvPolynomial.X =
      (MvPolynomial.X : α → MvPolynomial α (S ⊗[R] C)) := by
    funext i
    exact polynomialTensor_X i
  rw [hh]

noncomputable def tensorTruncateEquiv (q : ℕ) :
    S ⊗[R] Ring C α q ≃ₐ[S] Ring (S ⊗[R] C) α q :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (MvPolynomial α C) S
    (variablesIdeal C α ^ q)).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.rTensorAlgEquiv (R := R) (S := S))
      (polynomialTensor_ideal q).symm)

variable {D : Type*} [CommRing D]

lemma map_variables (f : C →+* D) :
    (variablesIdeal C α).map (MvPolynomial.map f) = variablesIdeal D α := by
  change (Ideal.span (Set.range (MvPolynomial.X : α → MvPolynomial α C))).map _ = _
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  ext i
  simp

noncomputable def mapEquiv (f : C ≃+* D) (q : ℕ) :
    Ring C α q ≃+* Ring D α q :=
  Ideal.quotientEquiv _ _ (MvPolynomial.mapEquiv α f)
    (by rw [Ideal.map_pow]; exact congrArg (· ^ q) (map_variables f.toRingHom).symm)

noncomputable def quotientTensorTruncateEquiv (I : Ideal R) (q : ℕ) :
    S ⊗[R] Ring (R ⧸ I) α q ≃+*
      Ring (S ⧸ I.map (algebraMap R S)) α q :=
  (tensorTruncateEquiv (R := R) (C := R ⧸ I) (S := S) (α := α) q).toRingEquiv.trans
    (mapEquiv (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toRingEquiv q)

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget
variable {R C D α : Type*} [CommRing R] [CommRing C] [CommRing D]
  [Algebra R C] [Algebra R D]

noncomputable def mapAlgEquiv (f : C ≃ₐ[R] D) (q : ℕ) :
    Ring C α q ≃ₐ[R] Ring D α q :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.mapAlgEquiv α f)
    (by rw [Ideal.map_pow]; exact congrArg (· ^ q) (map_variables f.toRingHom).symm)

variable {S : Type*} [CommRing S] [Algebra R S]
noncomputable def quotientTensorTruncateAlgEquiv (I : Ideal R) (q : ℕ) :
    TensorProduct R S (Ring (R ⧸ I) α q) ≃ₐ[S]
      Ring (S ⧸ I.map (algebraMap R S)) α q :=
  (tensorTruncateEquiv (R := R) (C := R ⧸ I) (S := S) (α := α) q).trans
    (mapAlgEquiv (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm q)

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
namespace TaylorShift
open TensorProduct
universe u
variable {K A α : Type u} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]

lemma coefficient_eq_algebraMap (I : Ideal A) (q : ℕ) :
    coefficient (α := α) I q = algebraMap A (Target (α := α) I q) := rfl

lemma coefficient_finite [Finite α] (I : Ideal A) (q : ℕ) (hq : 1 ≤ q) :
    Module.Finite A (Target (α := α) I q) := by
  apply TaylorTarget.finite_shifted (A ⧸ I) α A q hq
  intro a
  exact reduction_coefficient I q hq a

noncomputable def coefficientCompletionEquiv [IsNoetherianRing A] [Finite α]
    (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) :
    AdicCompletion (J.map (coefficient (α := α) I q)) (Target (α := α) I q) ≃+
      TaylorTarget.Ring ((AdicCompletion J A) ⧸ I.map (algebraMap A (AdicCompletion J A))) α q := by
  have : Module.Finite A (Target (α := α) I q) := coefficient_finite I q hq
  exact (CompletionScalar.tensorEquiv J).symm.toAddEquiv.trans
    (TaylorTarget.quotientTensorTruncateAlgEquiv
      (S := AdicCompletion J A) (α := α) I q).toRingEquiv.toAddEquiv

variable [Algebra.FormallySmooth (MvPolynomial α K) A]

noncomputable def shiftedTargetEquiv [IsNoetherianRing A] [Finite α]
    (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) :
    letI := (taylor (K := K) (α := α) I q hq).toAlgebra
    letI : Module A (Target (α := α) I q) :=
      (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
    TensorProduct A (AdicCompletion J A) (Target (α := α) I q) ≃+
      TaylorTarget.Ring ((AdicCompletion J A) ⧸ I.map (algebraMap A (AdicCompletion J A))) α q := by
  letI := (taylor (K := K) (α := α) I q hq).toAlgebra
  letI : Module A (Target (α := α) I q) :=
    (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
  have : Module.Finite A (Target (α := α) I q) := taylor_finite (K := K) (α := α) I q hq
  exact (CompletionScalar.tensorEquiv J).toAddEquiv.trans
    ((completionEquiv (K := K) I J q hq).toAddEquiv.trans
      (coefficientCompletionEquiv I J q hq))

end TaylorShift
end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget
open TensorProduct
variable {R S C D α : Type*} [CommRing R] [CommRing S] [CommRing C] [CommRing D]
  [Algebra R S]

noncomputable def map (f : C →+* D) (q : ℕ) : Ring C α q →+* Ring D α q :=
  Ideal.quotientMap _ (MvPolynomial.map f) (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, map_variables])

@[simp] lemma map_mk (f : C →+* D) (q : ℕ) (p : MvPolynomial α C) :
    map f q (mk C α q p) = mk D α q (MvPolynomial.map f p) := rfl

noncomputable def quotientCoefficient (I : Ideal R) :
    R ⧸ I →+* S ⧸ I.map (algebraMap R S) :=
  Ideal.quotientMap _ (algebraMap R S) Ideal.le_comap_map

lemma tensorQuotient_coefficient (I : Ideal R) (a : R ⧸ I) :
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm (1 ⊗ₜ[R] a) =
      quotientCoefficient (S := S) I a := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  change Ideal.Quotient.mk _ (a • (1 : S)) = Ideal.Quotient.mk _ (algebraMap R S a)
  rw [Algebra.smul_def, mul_one]

@[simp] lemma quotientTensorTruncateAlgEquiv_one_tmul (I : Ideal R) (q : ℕ)
    (t : Ring (R ⧸ I) α q) :
    quotientTensorTruncateAlgEquiv (S := S) I q (1 ⊗ₜ[R] t) =
      map (quotientCoefficient (S := S) I) q t := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective t
  change Ideal.Quotient.mk _
    (MvPolynomial.map (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toRingHom
      (MvPolynomial.rTensorAlgEquiv (1 ⊗ₜ[R] p))) =
    Ideal.Quotient.mk _ (MvPolynomial.map (quotientCoefficient (S := S) I) p)
  congr 1
  ext e
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_rTensorAlgEquiv_tmul]
  exact tensorQuotient_coefficient I _

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift
open TensorProduct
universe u
variable {K A α : Type u} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]

@[simp] lemma coefficientCompletionEquiv_of [IsNoetherianRing A] [Finite α]
    (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) (t : Target (α := α) I q) :
    coefficientCompletionEquiv I J q hq
      (AdicCompletion.of (J.map (coefficient (α := α) I q)) _ t) =
      TaylorTarget.map (TaylorTarget.quotientCoefficient (S := AdicCompletion J A) I) q t := by
  have : Module.Finite A (Target (α := α) I q) := coefficient_finite I q hq
  have ht : (CompletionScalar.tensorEquiv J).symm
      (AdicCompletion.of (J.map (coefficient (α := α) I q)) _ t) = 1 ⊗ₜ[A] t := by
    change (CompletionScalar.tensorEquiv J).symm
      (AdicCompletion.of (J.map (algebraMap A (Target (α := α) I q))) _ t) = _
    apply (CompletionScalar.tensorEquiv J).injective
    rw [LinearEquiv.apply_symm_apply, CompletionScalar.tensorEquiv_one_tmul]
  change TaylorTarget.quotientTensorTruncateAlgEquiv (S := AdicCompletion J A) I q
    ((CompletionScalar.tensorEquiv J).symm _) = _
  rw [ht,TaylorTarget.quotientTensorTruncateAlgEquiv_one_tmul]

variable [Algebra.FormallySmooth (MvPolynomial α K) A]

@[simp] lemma shiftedTargetEquiv_one_tmul [IsNoetherianRing A] [Finite α]
    (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) (t : Target (α := α) I q) :
    letI := (taylor (K := K) (α := α) I q hq).toAlgebra
    letI : Module A (Target (α := α) I q) :=
      (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
    shiftedTargetEquiv (K := K) I J q hq (1 ⊗ₜ[A] t) =
      TaylorTarget.map (TaylorTarget.quotientCoefficient (S := AdicCompletion J A) I) q t := by
  let := (taylor (K := K) (α := α) I q hq).toAlgebra
  let : Module A (Target (α := α) I q) :=
    (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
  have : Module.Finite A (Target (α := α) I q) := taylor_finite (K := K) (α := α) I q hq
  have ht := tensorCompletionEquiv_one_tmul (K := K) I J q hq t
  exact (congrArg (coefficientCompletionEquiv I J q hq) ht).trans
    (coefficientCompletionEquiv_of I J q hq t)

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionScalar
open TensorProduct
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

lemma equiv_smul_of (I : Ideal R) (r : AdicCompletion I R) (s : S) :
    equiv I (r • AdicCompletion.of I S s) =
      AdicFunctor.map I (I.map (algebraMap R S)) (algebraMap R S)
        Ideal.le_comap_map r * AdicCompletion.of (I.map (algebraMap R S)) S s := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [map_mul, AdicFunctor.eval_map, AdicCompletion.evalₐ_of]
  induction r using AdicCompletion.induction_on I R with
  | _ r =>
    have hv : (equiv I (AdicCompletion.mk I R r • AdicCompletion.of I S s)).val n =
        Submodule.Quotient.mk (p := ((I.map (algebraMap R S)) ^ n • ⊤ : Ideal S))
          (algebraMap R S (r.val n) * s) := by
      change quotientEquiv I n ((AdicCompletion.mk I R r •
        AdicCompletion.of I S s).val n) = _
      rw [AdicCompletion.smul_eval]
      change quotientEquiv I n (r.val n • Submodule.Quotient.mk s) = _
      rw [map_smul, quotientEquiv_mk, ← Submodule.Quotient.mk_smul]
      simp only [Algebra.smul_def]
    rw [← AdicCompletion.factor_eval_eq_evalₐ (I.map (algebraMap R S)) _
      (by rw [smul_eq_mul, Ideal.mul_top])]
    change Ideal.Quotient.factor
      (show (I.map (algebraMap R S)) ^ n • ⊤ ≤ (I.map (algebraMap R S)) ^ n from
        by rw [smul_eq_mul, Ideal.mul_top]) ((equiv I
      (AdicCompletion.mk I R r • AdicCompletion.of I S s)).val n) = _
    rw [hv, AdicCompletion.evalₐ_mk]
    simp only [AdicFunctor.quotient, Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk]
    rfl

lemma tensorEquiv_tmul [IsNoetherianRing R] [Module.Finite R S]
    (I : Ideal R) (r : AdicCompletion I R) (s : S) :
    tensorEquiv I (r ⊗ₜ[R] s) =
      AdicFunctor.map I (I.map (algebraMap R S)) (algebraMap R S)
        Ideal.le_comap_map r * AdicCompletion.of (I.map (algebraMap R S)) S s := by
  change equiv I (AdicCompletion.ofTensorProduct I S (r ⊗ₜ[R] s)) = _
  rw [AdicCompletion.ofTensorProduct_tmul, equiv_smul_of]

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionScalar

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
namespace TaylorShift
variable {K A α : Type*} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]
  [Algebra.FormallySmooth (MvPolynomial α K) A]

noncomputable def completedTaylor (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) :
    AdicCompletion J A →+*
      AdicCompletion (J.map (coefficient (α := α) I q)) (Target (α := α) I q) :=
  (completionEquiv (K := K) I J q hq).toRingHom.comp
    (AdicFunctor.map J (J.map (taylor (K := K) (α := α) I q hq))
      (taylor (K := K) (α := α) I q hq) Ideal.le_comap_map)

@[simp] theorem completedTaylor_of (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q)
    (a : A) :
    completedTaylor (K := K) I J q hq (AdicCompletion.of J A a) =
      AdicCompletion.of (J.map (coefficient (α := α) I q)) _
        (taylor (K := K) (α := α) I q hq a) := by
  change completionEquiv (K := K) I J q hq
    (AdicFunctor.map _ _ _ _ _) = _
  rw [AdicFunctor.map_of,completionEquiv_of]

end TaylorShift
end BoundaryOnly.FormalObstruction.AlgebraicReplacement

end

end OAI
