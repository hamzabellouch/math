import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.LocalOrigin
import OAI.Algebra.AlgebraicObstruction.TaylorTarget

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart
open MvPowerSeries
open BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {K α : Type} [Field K] [Finite α]

omit [Finite α] in
lemma origin_eq_variables : origin (K := K) (α := α) = MvPolynomial.idealOfVars α K :=
  (TaylorTarget.variables_ker K α).symm

omit [Finite α] in
lemma maximalIdeal_eq_map_variables (E : AffineEtaleChart K α) :
    IsLocalRing.maximalIdeal E.LocalRing =
      (MvPolynomial.idealOfVars α K).map (algebraMap (MvPolynomial α K) E.LocalRing) := by
  rw [maximalIdeal_eq_map_origin,origin_eq_variables]

def augmentation (E : AffineEtaleChart K α) : E.LocalRing →+* K :=
  constantCoeff.comp E.localExpansion.toRingHom

@[simp] lemma augmentation_polynomial (E : AffineEtaleChart K α) (p : MvPolynomial α K) :
    E.augmentation (algebraMap (MvPolynomial α K) E.LocalRing p) =
      MvPolynomial.constantCoeff p := by
  change constantCoeff (E.localExpansion (algebraMap (MvPolynomial α K) E.LocalRing p)) = _
  rw [E.localExpansion.commutes]
  rfl

lemma augmentation_ker (E : AffineEtaleChart K α) :
    RingHom.ker E.augmentation = IsLocalRing.maximalIdeal E.LocalRing := by
  ext a
  change E.augmentation a = 0 ↔ _
  rw [IsLocalRing.mem_maximalIdeal]
  constructor
  · intro h hu
    have hh := hu.map E.augmentation
    rw [h] at hh
    exact not_isUnit_zero hh
  · intro h
    by_contra hn
    apply h
    apply isUnit_of_map_unit E.localExpansion
    rw [MvPowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero]
    exact hn

abbrev FormalTruncation (q : ℕ) := TaylorTarget.Ring K α q

noncomputable def formalTruncate (q : ℕ) :
    MvPowerSeries α K →ₐ[MvPolynomial α K] FormalTruncation (K := K) (α := α) q :=
  MvPowerSeries.truncTotalAlgHom α K q

lemma reduction_formalTruncate (q : ℕ) (hq : 1 ≤ q) (f : MvPowerSeries α K) :
    TaylorTarget.reduction K α q hq (formalTruncate q f) = constantCoeff f := by
  change MvPolynomial.constantCoeff (MvPowerSeries.truncTotal q f) = constantCoeff f
  exact MvPowerSeries.coeff_truncTotal _ (by simp only [map_zero]; omega)

noncomputable def truncate (E : AffineEtaleChart K α) (q : ℕ) :
    E.LocalRing →ₐ[MvPolynomial α K] FormalTruncation (K := K) (α := α) q :=
  (formalTruncate q).comp E.localExpansion

@[simp] lemma truncate_polynomial (E : AffineEtaleChart K α) (q : ℕ) (p : MvPolynomial α K) :
    E.truncate q (algebraMap (MvPolynomial α K) E.LocalRing p) =
      Ideal.Quotient.mk (MvPolynomial.idealOfVars α K ^ q) p :=
  (E.truncate q).commutes p

lemma reduction_truncate (E : AffineEtaleChart K α) (q : ℕ) (hq : 1 ≤ q) (a : E.LocalRing) :
    TaylorTarget.reduction K α q hq (E.truncate q a) = E.augmentation a :=
  reduction_formalTruncate q hq _

lemma truncate_maximal_pow (E : AffineEtaleChart K α) (q : ℕ) :
    (IsLocalRing.maximalIdeal E.LocalRing) ^ q ≤ RingHom.ker (E.truncate q) := by
  rw [E.maximalIdeal_eq_map_variables,← Ideal.map_pow,Ideal.map_le_iff_le_comap]
  intro p hp
  change E.truncate q (algebraMap (MvPolynomial α K) E.LocalRing p) = 0
  rw [truncate_polynomial,Ideal.Quotient.eq_zero_iff_mem]
  exact hp

noncomputable def truncateQuotient (E : AffineEtaleChart K α) (q : ℕ) :
    E.LocalRing ⧸ (IsLocalRing.maximalIdeal E.LocalRing) ^ q →+*
       FormalTruncation (K := K) (α := α) q :=
  Ideal.Quotient.lift _ (E.truncate q).toRingHom (E.truncate_maximal_pow q)

noncomputable def polynomialQuotient (E : AffineEtaleChart K α) (q : ℕ) :
    FormalTruncation (K := K) (α := α) q →ₐ[MvPolynomial α K]
      E.LocalRing ⧸ (IsLocalRing.maximalIdeal E.LocalRing) ^ q :=
  Ideal.Quotient.liftₐ _ (Algebra.ofId (MvPolynomial α K) (E.LocalRing ⧸ (IsLocalRing.maximalIdeal E.LocalRing) ^ q)) (by
    intro p hp
    change Ideal.Quotient.mk _ (algebraMap (MvPolynomial α K) E.LocalRing p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem,E.maximalIdeal_eq_map_variables,← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hp)

lemma truncate_polynomialQuotient (E : AffineEtaleChart K α) (q : ℕ)
    (x : FormalTruncation (K := K) (α := α) q) :
    E.truncateQuotient q (E.polynomialQuotient q x) = x := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  change E.truncate q (algebraMap (MvPolynomial α K) E.LocalRing p) = _
  exact E.truncate_polynomial q p

lemma factor_polynomial_truncate (E : AffineEtaleChart K α) (q : ℕ) (hq : 1 ≤ q)
    (a : E.LocalRing) :
    Ideal.Quotient.factor (Ideal.pow_le_self (show q ≠ 0 by omega))
      (E.polynomialQuotient q (E.truncate q a)) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal E.LocalRing) a := by
  obtain ⟨p,hp⟩ := Ideal.Quotient.mk_surjective (E.truncate q a)
  have hc : MvPolynomial.constantCoeff p = E.augmentation a := by
    have hh := congrArg (TaylorTarget.reduction K α q hq) hp
    exact (TaylorTarget.reduction_mk K α q hq p).symm.trans
      (hh.trans (E.reduction_truncate q hq a))
  rw [← hp]
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal E.LocalRing)
      (algebraMap (MvPolynomial α K) E.LocalRing p) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal E.LocalRing) a
  rw [Ideal.Quotient.eq,← E.augmentation_ker]
  change E.augmentation (algebraMap (MvPolynomial α K) E.LocalRing p - a) = 0
  rw [map_sub,augmentation_polynomial,hc,sub_self]

lemma polynomial_truncate (E : AffineEtaleChart K α) (q : ℕ) (a : E.LocalRing) :
    E.polynomialQuotient q (E.truncate q a) =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal E.LocalRing)^q) a := by
  by_cases hq : q = 0
  · subst q
    have : Subsingleton (E.LocalRing ⧸ (IsLocalRing.maximalIdeal E.LocalRing)^0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact Subsingleton.elim _ _
  · let r := Ideal.Quotient.factor
      (Ideal.pow_le_self (I := IsLocalRing.maximalIdeal E.LocalRing) hq)
    have hr : IsNilpotent (RingHom.ker r) := by
      refine ⟨q,?_⟩
      have hk : RingHom.ker r = (IsLocalRing.maximalIdeal E.LocalRing).map
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal E.LocalRing)^q)) := by
        apply Ideal.comap_injective_of_surjective
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal E.LocalRing)^q)) Ideal.Quotient.mk_surjective
        rw [RingHom.comap_ker]
        change RingHom.ker (Ideal.Quotient.mk (IsLocalRing.maximalIdeal E.LocalRing)) = _
        rw [Ideal.mk_ker,Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
        change _ = IsLocalRing.maximalIdeal E.LocalRing ⊔ _
        rw [← RingHom.ker_eq_comap_bot,Ideal.mk_ker]
        exact (sup_eq_left.mpr (Ideal.pow_le_self hq)).symm
      rw [hk,← Ideal.map_pow,Ideal.map_quotient_self]
      rfl
    have hh := Algebra.FormallyUnramified.ext' r hr
      ((E.polynomialQuotient q).comp (E.truncate q))
      (Ideal.Quotient.mkₐ (MvPolynomial α K) ((IsLocalRing.maximalIdeal E.LocalRing)^q))
      (fun a ↦ E.factor_polynomial_truncate q (by omega) a)
    exact AlgHom.congr_fun hh a

noncomputable def truncatedEquiv (E : AffineEtaleChart K α) (q : ℕ) :
    E.LocalRing ⧸ (IsLocalRing.maximalIdeal E.LocalRing)^q ≃+*
      FormalTruncation (K := K) (α := α) q :=
  { E.truncateQuotient q with
    invFun := E.polynomialQuotient q
    left_inv := by
      intro x
      obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
      exact E.polynomial_truncate q a
    right_inv := E.truncate_polynomialQuotient q }

@[simp] lemma truncatedEquiv_mk (E : AffineEtaleChart K α) (q : ℕ) (a : E.LocalRing) :
    E.truncatedEquiv q (Ideal.Quotient.mk _ a) = E.truncate q a := rfl

end BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart

end

end OAI
