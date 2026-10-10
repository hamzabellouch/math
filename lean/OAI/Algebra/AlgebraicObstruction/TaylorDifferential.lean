import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.AlgebraicGerms
import OAI.Algebra.AlgebraicObstruction.TaylorCoefficients

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift
variable {K A α : Type*} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]
  [Algebra.FormallyEtale (MvPolynomial α K) A]

theorem shiftDeriv_taylor (I : Ideal A) (i : α) (q : ℕ) (hq : 1 ≤ q) (a : A) :
    TaylorTarget.shiftDeriv i q (taylor (K := K) (α := α) I (q+1) (by omega) a) =
      taylor (K := K) (α := α) I q hq
        (extendDerivation (T := A) (MvPolynomial.pderiv (R := K) i) a) := by
  classical
  let T := Target (α := α) I q
  let : Algebra A T := (taylor (K := K) (α := α) I q hq).toAlgebra
  let : SMul A T := (inferInstance : Algebra A T).toSMul
  let : Module A T := (inferInstance : Algebra A T).toModule
  let : SMul K T := (inferInstance : Algebra K T).toSMul
  let : Module K T := (inferInstance : Algebra K T).toModule
  let : IsScalarTower K A T := IsScalarTower.of_algebraMap_eq' (by
    ext k
    exact (taylor_scalar (K := K) (α := α) I q hq k).symm)
  let : Algebra (MvPolynomial α K) T := (shift (K := K) (α := α) I q).toAlgebra
  let : SMul (MvPolynomial α K) T := (inferInstance : Algebra (MvPolynomial α K) T).toSMul
  let : Module (MvPolynomial α K) T := (inferInstance : Algebra (MvPolynomial α K) T).toModule
  let : IsScalarTower (MvPolynomial α K) A T := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro p
    exact (taylor_coordinates (K := K) (α := α) I q hq p).symm)
  let : IsScalarTower K (MvPolynomial α K) T := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro k
    change TaylorTarget.mk (A ⧸ I) α q
      (MvPolynomial.C (Ideal.Quotient.mk I (algebraMap K A k))) =
        shift (K := K) (α := α) I q (MvPolynomial.C k)
    simp [shift])
  let d : Derivation K A T :=
    { toLinearMap := (TaylorTarget.shiftDerivLinear (K := K) i q).comp
        (taylorAlgHom (K := K) (α := α) I (q+1) (by omega)).toLinearMap
      map_one_eq_zero' := by
        change TaylorTarget.shiftDeriv i q (taylor (K := K) (α := α) I (q+1) (by omega) 1) = 0
        rw [map_one,TaylorTarget.shiftDeriv_one]
      leibniz' := by
        intro x y
        change TaylorTarget.shiftDeriv i q (taylor (K := K) (α := α) I (q+1) (by omega) (x*y)) =
          taylor (K := K) (α := α) I q hq x *
            TaylorTarget.shiftDeriv i q (taylor (K := K) (α := α) I (q+1) (by omega) y) +
          taylor (K := K) (α := α) I q hq y *
            TaylorTarget.shiftDeriv i q (taylor (K := K) (α := α) I (q+1) (by omega) x)
        rw [map_mul,TaylorTarget.shiftDeriv_mul,lower_taylor I q hq,lower_taylor I q hq] }
  let e : Derivation K A T := (Algebra.linearMap A T).compDer
    (extendDerivation (T := A) (MvPolynomial.pderiv (R := K) i))
  have he : d.compAlgebraMap (MvPolynomial α K) = e.compAlgebraMap (MvPolynomial α K) := by
    apply MvPolynomial.derivation_ext
    intro j
    change TaylorTarget.shiftDeriv i q
      (taylor (K := K) (α := α) I (q+1) (by omega)
        (algebraMap (MvPolynomial α K) A (MvPolynomial.X j))) =
      taylor (K := K) (α := α) I q hq
        (extendDerivation (T := A) (MvPolynomial.pderiv (R := K) i)
          (algebraMap (MvPolynomial α K) A (MvPolynomial.X j)))
    rw [taylor_coordinates,extendDerivation_algebraMap,taylor_coordinates]
    simp only [shift,MvPolynomial.eval₂Hom_X']
    rw [TaylorTarget.shiftDeriv_mk]
    by_cases hij : j = i
    · subst j
      simp
    · simp [MvPolynomial.pderiv_X_of_ne hij]
  have hde : d = e := etale_derivation_ext d e (fun p ↦ Derivation.congr_fun he p)
  exact Derivation.congr_fun hde a

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift

namespace BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart
open MvPowerSeries BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {K α : Type} [Field K] [Finite α]

noncomputable def completionDeriv (E : AffineEtaleChart K α) (i : α) :
    AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing →+
      AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing :=
  E.completionEquiv.symm.toAddMonoidHom.comp
    ((pderiv (R := K) i).toAddMonoidHom.comp E.completionEquiv.toAddMonoidHom)

@[simp] theorem completionDeriv_of (E : AffineEtaleChart K α) (i : α) (a : E.LocalRing) :
    E.completionDeriv i (AdicCompletion.of _ _ a) = AdicCompletion.of _ _ (E.deriv i a) := by
  apply E.completionEquiv.injective
  change E.completionEquiv (E.completionEquiv.symm (pderiv (R := K) i
    (E.completionEquiv (AdicCompletion.of _ _ a)))) = _
  rw [E.completionEquiv.apply_symm_apply,E.completionEquiv_of,E.completionEquiv_of,
    E.expansion_deriv]

theorem completionDeriv_mem_pow (E : AffineEtaleChart K α) (i : α) (N : ℕ)
    (b : AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing)
    (hb : b ∈ (IsLocalRing.maximalIdeal _ : Ideal
      (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing))^(N+1)) :
    E.completionDeriv i b ∈ (IsLocalRing.maximalIdeal _)^N := by
  have hh := Ideal.mem_map_of_mem E.completionEquiv.toRingHom hb
  rw [Ideal.map_pow] at hh
  have he : (IsLocalRing.maximalIdeal _).map E.completionEquiv.toRingHom =
      IsLocalRing.maximalIdeal _ := IsLocalRing.map_ringEquiv_maximalIdeal E.completionEquiv
  rw [he] at hh
  have hd := derivation_mem_pow (pderiv (R := K) i) (IsLocalRing.maximalIdeal _) N hh
  have ht := Ideal.mem_map_of_mem E.completionEquiv.symm.toRingHom hd
  rw [Ideal.map_pow] at ht
  have he' : (IsLocalRing.maximalIdeal _).map E.completionEquiv.symm.toRingHom =
      IsLocalRing.maximalIdeal _ := IsLocalRing.map_ringEquiv_maximalIdeal E.completionEquiv.symm
  rw [he'] at ht
  exact ht

end BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget
variable {R S α : Type*} [CommRing R] [CommRing S]

lemma shiftDeriv_map (f : R →+* S) (q : ℕ) (i : α) (x : Ring R α (q+1)) :
    shiftDeriv i q (map f (q+1) x) = map f q (shiftDeriv i q x) := by
  obtain ⟨p,rfl⟩ := mk_surjective (q+1) x
  rw [map_mk,shiftDeriv_mk,shiftDeriv_mk,map_mk,MvPolynomial.pderiv_map]

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorTarget

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift
variable {A α : Type} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Finite α]

lemma coefficient_adic_separated (I : Ideal A) (q : ℕ) (hq : 1 ≤ q)
    (x y : Target (α := α) I q)
    (h : ∀ N, x-y ∈ ((IsLocalRing.maximalIdeal A).map
      (algebraMap A (Target (α := α) I q)))^N) : x = y := by
  have : Module.Finite A (Target (α := α) I q) := coefficient_finite I q hq
  apply (IsHausdorff.eq_iff_smodEq (I := IsLocalRing.maximalIdeal A)).mpr
  intro N
  rw [SModEq.sub_mem,Ideal.smul_top_eq_map,Submodule.restrictScalars_mem,Ideal.map_pow]
  exact h N

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift

namespace BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart
open MvPowerSeries BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {K α : Type} [Field K] [Finite α]

instance completionNoetherian (E : AffineEtaleChart K α) :
    IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing) :=
  isNoetherianRing_of_ringEquiv (MvPowerSeries α K) E.completionEquiv.symm

end BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {A B T : Type*} [AddCommGroup A] [CommRing B] [CommRing T]

lemma additive_eq_of_approximation (f : A →+ B) (F G : B →+ T)
    (J : Ideal B) (H : Ideal T) (q : ℕ)
    (hdense : ∀ b N, ∃ a, b-f a ∈ J^N)
    (hsep : ∀ x y, (∀ N, x-y ∈ H^N) → x=y)
    (hF : ∀ N b, b ∈ J^(N+q) → F b ∈ H^N)
    (hG : ∀ N b, b ∈ J^(N+q) → G b ∈ H^N)
    (hag : ∀ a, F (f a) = G (f a)) (b : B) : F b = G b := by
  apply hsep
  intro N
  obtain ⟨a,ha⟩ := hdense b (N+q)
  have h := (H^N).sub_mem (hF N _ ha) (hG N _ ha)
  rw [map_sub,map_sub,hag] at h
  convert h using 1
  abel

end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart
open MvPowerSeries BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {K α : Type} [Field K] [Finite α]

theorem fullTaylor_deriv_of (E : AffineEtaleChart K α) (I : Ideal E.LocalRing)
    (i : α) (q : ℕ) (hq : 1 ≤ q) (a : E.LocalRing) :
    TaylorTarget.shiftDeriv i q
      (TaylorShift.fullTaylor (K := K) (α := α) I (IsLocalRing.maximalIdeal E.LocalRing)
        (q+1) (by omega) (AdicCompletion.of _ _ a)) =
      TaylorShift.fullTaylor (K := K) (α := α) I (IsLocalRing.maximalIdeal E.LocalRing)
        q hq (AdicCompletion.of _ _ (E.deriv i a)) := by
  rw [TaylorShift.fullTaylor_of,TaylorTarget.shiftDeriv_map,
    TaylorShift.shiftDeriv_taylor I i q hq,TaylorShift.fullTaylor_of]
  rfl

theorem fullTaylor_deriv (E : AffineEtaleChart K α) (I : Ideal E.LocalRing)
    (i : α) (q : ℕ) (hq : 1 ≤ q)
    (b : AdicCompletion (IsLocalRing.maximalIdeal E.LocalRing) E.LocalRing) :
    TaylorTarget.shiftDeriv i q
      (TaylorShift.fullTaylor (K := K) (α := α) I (IsLocalRing.maximalIdeal E.LocalRing)
        (q+1) (by omega) b) =
    TaylorShift.fullTaylor (K := K) (α := α) I (IsLocalRing.maximalIdeal E.LocalRing)
        q hq (E.completionDeriv i b) := by
  let J := IsLocalRing.maximalIdeal E.LocalRing
  let B := AdicCompletion J E.LocalRing
  let R := I.map (algebraMap E.LocalRing B)
  let m := IsLocalRing.maximalIdeal B
  let T := TaylorTarget.Ring (B ⧸ R) α q
  let F := (TaylorTarget.shiftDerivLinear (K := B ⧸ R) i q).toAddMonoidHom.comp
    (TaylorShift.fullTaylor (K := K) (α := α) I J (q+1) (by omega)).toAddMonoidHom
  let G := (TaylorShift.fullTaylor (K := K) (α := α) I J q hq).toAddMonoidHom.comp
    (E.completionDeriv i)
  have hm : m = J.map (algebraMap E.LocalRing B) :=
    AdicCompletion.maximalIdeal_eq_map
  apply additive_eq_of_approximation (AdicCompletion.of J E.LocalRing).toAddMonoidHom
    F G m (m.map (algebraMap B T)) q
  · intro b N
    rw [hm]
    exact completion_approximate J b N
  · exact fun x y h ↦ TaylorShift.coefficient_adic_separated R q hq x y h
  · intro N x hx
    change TaylorTarget.shiftDeriv i q
      (TaylorShift.fullTaylor (K := K) (α := α) I J (q+1) (by omega) x) ∈ _
    rw [hm] at hx ⊢
    apply TaylorTarget.shiftDeriv_mem_coeff_pow
    apply TaylorShift.fullTaylor_mem_pow (K := K) (α := α) I J (q+1) (by omega) N x
    rwa [show N+(q+1)-1 = N+q by omega]
  · intro N x hx
    change TaylorShift.fullTaylor (K := K) (α := α) I J q hq (E.completionDeriv i x) ∈ _
    have hD := E.completionDeriv_mem_pow i (N+q-1) x (by
      rw [show N+q-1+1 = N+q by omega]
      exact hx)
    change E.completionDeriv i x ∈ m^(N+q-1) at hD
    rw [hm] at hD ⊢
    exact TaylorShift.fullTaylor_mem_pow (K := K) (α := α) I J q hq N _ hD
  · intro a
    dsimp only [F,G,AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe]
    exact (E.fullTaylor_deriv_of I i q hq a).trans
      (congrArg (TaylorShift.fullTaylor (K := K) (α := α) I J q hq)
        (E.completionDeriv_of i a).symm)

end BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart

end

end OAI
