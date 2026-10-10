import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.TaylorCompletion
import OAI.Algebra.AlgebraicObstruction.FlatDescent
import OAI.Algebra.AlgebraicObstruction.AlgebraicGerms

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift
open TensorProduct
universe u
variable {K A α : Type u} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]
  [Algebra.FormallySmooth (MvPolynomial α K) A]
  [IsNoetherianRing A] [Finite α]

@[simp] theorem tensorCompletionEquiv_tmul_one
    (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) (b : AdicCompletion J A) :
    letI := (taylor (K := K) (α := α) I q hq).toAlgebra
    letI : Module A (Target (α := α) I q) :=
      (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
    tensorCompletionEquiv (K := K) (α := α) I J q hq (b ⊗ₜ[A] 1) =
      completedTaylor (K := K) (α := α) I J q hq b := by
  let := (taylor (K := K) (α := α) I q hq).toAlgebra
  let : Module A (Target (α := α) I q) :=
    (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
  have : Module.Finite A (Target (α := α) I q) := taylor_finite (K := K) (α := α) I q hq
  have ht := CompletionScalar.tensorEquiv_tmul J b (1 : Target (α := α) I q)
  change CompletionScalar.tensorEquiv J (b ⊗ₜ[A] (1 : Target (α := α) I q)) =
    AdicFunctor.map J (J.map (taylor (K := K) (α := α) I q hq))
      (taylor (K := K) (α := α) I q hq) Ideal.le_comap_map b * 1 at ht
  rw [mul_one] at ht
  exact congrArg (completionEquiv (K := K) (α := α) I J q hq) ht

@[simp] theorem shiftedTargetEquiv_tmul_one
    (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) (b : AdicCompletion J A) :
    letI := (taylor (K := K) (α := α) I q hq).toAlgebra
    letI : Module A (Target (α := α) I q) :=
      (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
    shiftedTargetEquiv (K := K) (α := α) I J q hq (b ⊗ₜ[A] 1) =
      coefficientCompletionEquiv (α := α) I J q hq (completedTaylor (K := K) (α := α) I J q hq b) := by
  let := (taylor (K := K) (α := α) I q hq).toAlgebra
  let : Module A (Target (α := α) I q) :=
    (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
  have : Module.Finite A (Target (α := α) I q) := taylor_finite (K := K) (α := α) I q hq
  exact congrArg (coefficientCompletionEquiv (α := α) I J q hq)
    (tensorCompletionEquiv_tmul_one (K := K) (α := α) I J q hq b)

theorem actual_whole_tuple_descends (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q)
    [Module.FaithfullyFlat A (AdicCompletion J A)]
    (b : AdicCompletion J A) (x : Target (α := α) I q)
    (hx : coefficientCompletionEquiv (α := α) I J q hq
        (completedTaylor (K := K) (α := α) I J q hq b) =
      TaylorTarget.map (TaylorTarget.quotientCoefficient (S := AdicCompletion J A) I) q x) :
    ∃ a : A, taylor (K := K) (α := α) I q hq a = x := by
  let := (taylor (K := K) (α := α) I q hq).toAlgebra
  let : Module A (Target (α := α) I q) :=
    (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
  have htx : b ⊗ₜ[A] (1 : Target (α := α) I q) = 1 ⊗ₜ[A] x := by
    apply (shiftedTargetEquiv (K := K) (α := α) I J q hq).injective
    rw [shiftedTargetEquiv_tmul_one, shiftedTargetEquiv_one_tmul]
    exact hx
  let f := Algebra.linearMap A (Target (α := α) I q)
  apply whole_tuple_descends (B := AdicCompletion J A) f x
  rw [← htx]
  refine ⟨b ⊗ₜ[A] (⟨1, ?_⟩ : LinearMap.range f), ?_⟩
  · exact ⟨1, map_one (taylor (K := K) (α := α) I q hq)⟩
  · rfl

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift
open TensorProduct
universe u
variable {K A α : Type u} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]
  [Algebra.FormallySmooth (MvPolynomial α K) A]
  [IsNoetherianRing A] [Finite α]

theorem completedTaylor_eq_zero_iff (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q)
    [Module.FaithfullyFlat A (AdicCompletion J A)] (b : AdicCompletion J A) :
    completedTaylor (K := K) (α := α) I J q hq b = 0 ↔
      b ∈ (RingHom.ker (taylor (K := K) (α := α) I q hq)).map
        (algebraMap A (AdicCompletion J A)) := by
  let := (taylor (K := K) (α := α) I q hq).toAlgebra
  let : Module A (Target (α := α) I q) :=
    (taylor (K := K) (α := α) I q hq).toAlgebra.toModule
  let f := Algebra.linearMap A (Target (α := α) I q)
  have hker : LinearMap.ker f = RingHom.ker (taylor (K := K) (α := α) I q hq) := rfl
  rw [← tmul_one_mem_ideal_baseChange_iff, ← hker, kernel_baseChange]
  change _ ↔ f.baseChange (AdicCompletion J A) (b ⊗ₜ[A] (1 : A)) = 0
  have hf : f (1 : A) = (1 : Target (α := α) I q) :=
    map_one (taylor (K := K) (α := α) I q hq)
  rw [LinearMap.baseChange_tmul, hf]
  rw [← tensorCompletionEquiv_tmul_one (K := K) (α := α) I J q hq]
  exact (tensorCompletionEquiv (K := K) (α := α) I J q hq).map_eq_zero_iff

theorem actual_primitive_tuple (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q)
    [Module.FaithfullyFlat A (AdicCompletion J A)]
    (b : AdicCompletion J A) (x : Target (α := α) I q)
    (hx : coefficientCompletionEquiv (α := α) I J q hq
        (completedTaylor (K := K) (α := α) I J q hq b) =
      TaylorTarget.map (TaylorTarget.quotientCoefficient (S := AdicCompletion J A) I) q x) :
    ∃ a : A, taylor (K := K) (α := α) I q hq a = x ∧
      b - AdicCompletion.of J A a ∈
        (RingHom.ker (taylor (K := K) (α := α) I q hq)).map
          (algebraMap A (AdicCompletion J A)) := by
  obtain ⟨a,ha⟩ := actual_whole_tuple_descends (K := K) (α := α) I J q hq b x hx
  refine ⟨a,ha, (completedTaylor_eq_zero_iff (K := K) (α := α) I J q hq _).mp ?_⟩
  rw [map_sub, sub_eq_zero, completedTaylor_of, ha]
  apply (coefficientCompletionEquiv (α := α) I J q hq).injective
  rw [coefficientCompletionEquiv_of]
  exact hx

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift

namespace BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart
open MvPowerSeries
variable {K α : Type} [Field K] [Finite α]

theorem completionFaithfullyFlat (E : AffineEtaleChart K α) :
    Module.FaithfullyFlat E.LocalRing
      (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing) := by
  have := E.localFaithfullyFlat
  exact Module.FaithfullyFlat.of_linearEquiv _ _ E.completionAlgEquiv.toLinearEquiv

theorem taylor_primitive_tuple (E : AffineEtaleChart K α) (I : Ideal E.LocalRing)
    (q : ℕ) (hq : 1 ≤ q)
    (b : AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)
    (x : BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift.Target (α := α) I q)
    (hx : BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift.coefficientCompletionEquiv
        (α := α) I (IsLocalRing.maximalIdeal E.LocalRing) q hq
        (BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift.completedTaylor
          (K := K) (α := α) I (IsLocalRing.maximalIdeal E.LocalRing) q hq b) =
      BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget.map
        (BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget.quotientCoefficient
          (S := AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing) I) q x) :
    ∃ a : E.LocalRing,
      BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift.taylor (K := K) (α := α) I q hq a = x ∧
      b - AdicCompletion.of _ _ a ∈
        (RingHom.ker (BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift.taylor
          (K := K) (α := α) I q hq)).map
          (algebraMap E.LocalRing
            (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)) := by
  have := E.completionFaithfullyFlat
  exact BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift.actual_primitive_tuple
    I (IsLocalRing.maximalIdeal E.LocalRing) q hq b x hx

end BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionScalar
open TensorProduct
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing R] [Module.Finite R S]

lemma tensorEquiv_one (I : Ideal R) :
    tensorEquiv I (1 : TensorProduct R (AdicCompletion I R) S) = 1 := by
  change tensorEquiv I (1 ⊗ₜ[R] (1 : S)) = 1
  rw [tensorEquiv_one_tmul]
  exact map_one (algebraMap S (AdicCompletion (I.map (algebraMap R S)) S))

lemma tensorEquiv_mul (I : Ideal R)
    (x y : TensorProduct R (AdicCompletion I R) S) :
    tensorEquiv I (x*y) = tensorEquiv I x * tensorEquiv I y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [add_mul,map_add,hx,hz]
  | tmul r s =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [mul_add,map_add,hy,hz]
    | tmul t u =>
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        simp only [tensorEquiv_tmul,map_mul]
        have hm : AdicCompletion.of (I.map (algebraMap R S)) S (s*u) =
            AdicCompletion.of (I.map (algebraMap R S)) S s *
              AdicCompletion.of (I.map (algebraMap R S)) S u :=
          map_mul (algebraMap S (AdicCompletion (I.map (algebraMap R S)) S)) s u
        rw [hm]
        ring

noncomputable def tensorRingEquiv (I : Ideal R) :
    TensorProduct R (AdicCompletion I R) S ≃+*
      AdicCompletion (I.map (algebraMap R S)) S :=
  { (tensorEquiv I).toAddEquiv with
    map_mul' := tensorEquiv_mul I }

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.CompletionScalar

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift
universe u
variable {K A α : Type u} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]
  [IsNoetherianRing A] [Finite α]

noncomputable def coefficientCompletionRingEquiv (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) :
    AdicCompletion (J.map (coefficient (α := α) I q)) (Target (α := α) I q) ≃+*
      TaylorTarget.Ring ((AdicCompletion J A) ⧸ I.map (algebraMap A (AdicCompletion J A))) α q := by
  haveI : Module.Finite A (Target (α := α) I q) := coefficient_finite I q hq
  exact (CompletionScalar.tensorRingEquiv J).symm.trans
    (TaylorTarget.quotientTensorTruncateAlgEquiv
      (S := AdicCompletion J A) (α := α) I q).toRingEquiv

lemma coefficientCompletionRingEquiv_apply (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q)
    (t : AdicCompletion (J.map (coefficient (α := α) I q)) (Target (α := α) I q)) :
    coefficientCompletionRingEquiv I J q hq t = coefficientCompletionEquiv I J q hq t := rfl

variable [Algebra.FormallySmooth (MvPolynomial α K) A]

noncomputable def fullTaylor (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) :
    AdicCompletion J A →+*
      TaylorTarget.Ring ((AdicCompletion J A) ⧸ I.map (algebraMap A (AdicCompletion J A))) α q :=
  (coefficientCompletionRingEquiv I J q hq).toRingHom.comp
    (completedTaylor (K := K) (α := α) I J q hq)

@[simp] theorem fullTaylor_of (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) (a : A) :
    fullTaylor (K := K) (α := α) I J q hq (AdicCompletion.of J A a) =
      TaylorTarget.map (TaylorTarget.quotientCoefficient (S := AdicCompletion J A) I) q
        (taylor (K := K) (α := α) I q hq a) := by
  change coefficientCompletionRingEquiv I J q hq (completedTaylor (K := K) I J q hq _) = _
  rw [coefficientCompletionRingEquiv_apply,completedTaylor_of,coefficientCompletionEquiv_of]

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift

end

end OAI
