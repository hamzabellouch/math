import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.ChartTruncation
import OAI.Algebra.AlgebraicObstruction.AdicFunctor

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart
open MvPowerSeries
open BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {K α : Type} [Field K] [Finite α]

lemma truncatedEquiv_compatible (E : AffineEtaleChart K α) {m n : ℕ} (h : m ≤ n)
    (x : E.LocalRing ⧸ (IsLocalRing.maximalIdeal E.LocalRing)^n) :
    Ideal.Quotient.factorPow (MvPolynomial.idealOfVars α K) h (E.truncatedEquiv n x) =
      E.truncatedEquiv m (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal E.LocalRing) h x) := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (MvPolynomial.idealOfVars α K ^ m)
      (truncTotal n (E.localExpansion a)) =
    Ideal.Quotient.mk (MvPolynomial.idealOfVars α K ^ m)
      (truncTotal m (E.localExpansion a))
  rw [Ideal.Quotient.eq]
  exact truncTotal_sub_truncTotal_mem_pow_idealOfVars h le_rfl _

def completionFamily (E : AffineEtaleChart K α) (n : ℕ) :
    AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing →+*
      FormalTruncation (K := K) (α := α) n :=
  (E.truncatedEquiv n).toRingHom.comp
    (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal E.LocalRing) n).toRingHom

lemma completionFamily_compatible (E : AffineEtaleChart K α) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars α K) h).comp (E.completionFamily n) =
      E.completionFamily m := by
  apply RingHom.ext
  intro x
  change Ideal.Quotient.factorPow _ h (E.truncatedEquiv n (AdicCompletion.evalₐ _ n x)) = _
  rw [E.truncatedEquiv_compatible h,AdicCofinal.factor_eval]
  rfl

noncomputable def completionToPolynomial (E : AffineEtaleChart K α) :
    AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing →+*
      AdicCompletion (MvPolynomial.idealOfVars α K) (MvPolynomial α K) :=
  AdicCompletion.liftRingHom _ E.completionFamily E.completionFamily_compatible

@[simp] lemma eval_completionToPolynomial (E : AffineEtaleChart K α) (n : ℕ)
    (x : AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing) :
    AdicCompletion.evalₐ _ n (E.completionToPolynomial x) =
      E.truncatedEquiv n (AdicCompletion.evalₐ _ n x) :=
  AdicCompletion.evalₐ_liftRingHom _ E.completionFamily E.completionFamily_compatible n x

omit [Finite α] in
lemma variables_le_comap_maximal (E : AffineEtaleChart K α) :
    MvPolynomial.idealOfVars α K ≤ (IsLocalRing.maximalIdeal E.LocalRing).comap
      (algebraMap (MvPolynomial α K) E.LocalRing) := by
  rw [E.maximalIdeal_eq_map_variables]
  exact Ideal.le_comap_map

noncomputable def polynomialToCompletion (E : AffineEtaleChart K α) :
    AdicCompletion (MvPolynomial.idealOfVars α K) (MvPolynomial α K) →+*
      AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing :=
  AdicFunctor.map _ _ (algebraMap (MvPolynomial α K) E.LocalRing) E.variables_le_comap_maximal

omit [Finite α] in
lemma quotient_polynomial (E : AffineEtaleChart K α) (n : ℕ)
    (x : FormalTruncation (K := K) (α := α) n) :
    AdicFunctor.quotient _ _ (algebraMap (MvPolynomial α K) E.LocalRing)
      E.variables_le_comap_maximal n x = E.polynomialQuotient n x := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

omit [Finite α] in
@[simp] lemma eval_polynomialToCompletion (E : AffineEtaleChart K α) (n : ℕ)
    (x : AdicCompletion (MvPolynomial.idealOfVars α K) (MvPolynomial α K)) :
    AdicCompletion.evalₐ _ n (E.polynomialToCompletion x) =
      E.polynomialQuotient n (AdicCompletion.evalₐ _ n x) := by
  rw [polynomialToCompletion,AdicFunctor.eval_map,quotient_polynomial]

lemma completionToPolynomial_polynomialToCompletion (E : AffineEtaleChart K α)
    (x : AdicCompletion (MvPolynomial.idealOfVars α K) (MvPolynomial α K)) :
    E.completionToPolynomial (E.polynomialToCompletion x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_completionToPolynomial,eval_polynomialToCompletion]
  exact (E.truncatedEquiv n).apply_symm_apply _

lemma polynomialToCompletion_completionToPolynomial (E : AffineEtaleChart K α)
    (x : AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing) :
    E.polynomialToCompletion (E.completionToPolynomial x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_polynomialToCompletion,eval_completionToPolynomial]
  exact (E.truncatedEquiv n).symm_apply_apply _

noncomputable def polynomialCompletionEquiv (E : AffineEtaleChart K α) :
    AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing ≃+*
      AdicCompletion (MvPolynomial.idealOfVars α K) (MvPolynomial α K) :=
  { E.completionToPolynomial with
    invFun := E.polynomialToCompletion
    left_inv := E.polynomialToCompletion_completionToPolynomial
    right_inv := E.completionToPolynomial_polynomialToCompletion }

noncomputable def completionEquiv (E : AffineEtaleChart K α) :
    AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing ≃+*
      MvPowerSeries α K :=
  E.polynomialCompletionEquiv.trans (MvPowerSeries.toAdicCompletionAlgEquiv α K).symm.toRingEquiv

@[simp] theorem completionEquiv_of (E : AffineEtaleChart K α) (a : E.LocalRing) :
    E.completionEquiv (AdicCompletion.of _ _ a) = E.localExpansion a := by
  apply (MvPowerSeries.toAdicCompletionAlgEquiv α K).injective
  change (MvPowerSeries.toAdicCompletionAlgEquiv α K)
    ((MvPowerSeries.toAdicCompletionAlgEquiv α K).symm
      (E.completionToPolynomial (AdicCompletion.of _ _ a))) = _
  rw [AlgEquiv.apply_symm_apply]
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_completionToPolynomial,AdicCompletion.evalₐ_of,truncatedEquiv_mk]
  rfl

noncomputable def completionAlgEquiv (E : AffineEtaleChart K α) :
    AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing ≃ₐ[E.LocalRing]
      MvPowerSeries α K :=
  { E.completionEquiv with commutes' := E.completionEquiv_of }

instance localNoetherian (E : AffineEtaleChart K α) : IsNoetherianRing E.LocalRing := by
  have : IsNoetherianRing E.S :=
    Algebra.FiniteType.isNoetherianRing (MvPolynomial α K) E.S
  infer_instance

end BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart

end

end OAI
