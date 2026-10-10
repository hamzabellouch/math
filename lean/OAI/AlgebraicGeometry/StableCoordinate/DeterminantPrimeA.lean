import OAI.AlgebraicGeometry.StableCoordinate.ObstructionDomains
import Mathlib.RingTheory.MvPolynomial.Basic

namespace OAI

/-!
# The first determinant coordinate is prime

This file proves the exact residual presentation obtained by setting `a=0`,
then its domain property. Consequently `a` is a prime element of the determinant
ring. Combined with the explicit `a`-chart, this is the algebraic input to the
prime-element localization criterion for unique factorization.
-/

namespace StableCoordinate.DeterminantPrimeA

open MvPolynomial
open DeterminantRing

noncomputable section

variable (k : Type*) [CommRing k]

/-- The residual relation after setting `a=0`; variables are `d,b,c,u`. -/
def residualRelation : MvPolynomial (Fin 4) k := X 1 * X 0 + 1

def residualIdeal : Ideal (MvPolynomial (Fin 4) k) := Ideal.span {residualRelation k}
abbrev ResidualRing := MvPolynomial (Fin 4) k ⧸ residualIdeal k

def residualMk : MvPolynomial (Fin 4) k →ₐ[k] ResidualRing k :=
  Ideal.Quotient.mkₐ k (residualIdeal k)

def rX (i : Fin 4) : ResidualRing k := residualMk k (X i)

theorem residual_relation : rX k 1 * rX k 0 + 1 = 0 := by
  have h : residualMk k (residualRelation k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa [residualRelation, rX] using h

def aIdeal : Ideal (C k) := Ideal.span {a k}
abbrev ModA := C k ⧸ aIdeal k

def modAMk : C k →ₐ[k] ModA k := Ideal.Quotient.mkₐ k (aIdeal k)

@[simp] theorem modAMk_a : modAMk k (a k) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem modA_relation : modAMk k (b k) * modAMk k (d k) + 1 = 0 := by
  have h := congrArg (modAMk k) (determinant_relation k)
  simp only [map_sub, map_mul, map_one, modAMk_a] at h
  linear_combination -h

def toResidual : C k →ₐ[k] ResidualRing k :=
  DeterminantRing.lift (k := k) 0 (rX k 0) (rX k 1) (rX k 2) (rX k 3) (by
    have h := residual_relation k
    linear_combination -h)

@[simp] theorem toResidual_a : toResidual k (a k) = 0 := by simp [toResidual]
@[simp] theorem toResidual_d : toResidual k (d k) = rX k 0 := by simp [toResidual]
@[simp] theorem toResidual_b : toResidual k (b k) = rX k 1 := by simp [toResidual]
@[simp] theorem toResidual_c : toResidual k (c k) = rX k 2 := by simp [toResidual]
@[simp] theorem toResidual_u : toResidual k (u k) = rX k 3 := by simp [toResidual]

def modAToResidual : ModA k →ₐ[k] ResidualRing k :=
  Ideal.Quotient.liftₐ (aIdeal k) (toResidual k) (by
    intro p hp
    have h : aIdeal k ≤ RingHom.ker (toResidual k).toRingHom := by
      rw [aIdeal, Ideal.span_singleton_le_iff_mem]
      simp [RingHom.mem_ker]
    exact h hp)

@[simp] theorem modAToResidual_mk (p : C k) :
    modAToResidual k (modAMk k p) = toResidual k p := rfl

def residualToModA : ResidualRing k →ₐ[k] ModA k :=
  Ideal.Quotient.liftₐ (residualIdeal k)
    (aeval ![modAMk k (d k), modAMk k (b k), modAMk k (c k), modAMk k (u k)]) (by
      intro p hp
      have h : residualIdeal k ≤ RingHom.ker
          (aeval ![modAMk k (d k), modAMk k (b k), modAMk k (c k), modAMk k (u k)]).toRingHom := by
        rw [residualIdeal, Ideal.span_singleton_le_iff_mem]
        simp [RingHom.mem_ker, residualRelation, modA_relation]
      exact h hp)

@[simp] theorem residualToModA_rX (i : Fin 4) :
    residualToModA k (rX k i) =
      (![modAMk k (d k), modAMk k (b k), modAMk k (c k), modAMk k (u k)] : Fin 4 → ModA k) i := by
  change (aeval ![modAMk k (d k), modAMk k (b k), modAMk k (c k), modAMk k (u k)]) (X i) = _
  simp

theorem residualToModA_comp_modAToResidual :
    (residualToModA k).comp (modAToResidual k) = AlgHom.id k (ModA k) := by
  apply Ideal.Quotient.algHom_ext
  apply DeterminantRing.hom_ext (k := k) (S := ModA k)
  all_goals
    change residualToModA k (modAToResidual k (modAMk k _)) = modAMk k _
    simp

theorem modAToResidual_comp_residualToModA :
    (modAToResidual k).comp (residualToModA k) = AlgHom.id k (ResidualRing k) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change modAToResidual k (residualToModA k (rX k i)) = rX k i
  fin_cases i <;> simp

/-- Setting `a=0` gives the domain presentation `k[d,b,c,u]/(bd+1)`. -/
def modAEquivResidual : ModA k ≃ₐ[k] ResidualRing k :=
  AlgEquiv.ofAlgHom (modAToResidual k) (residualToModA k)
    (modAToResidual_comp_residualToModA k) (residualToModA_comp_modAToResidual k)

section Domain
variable [IsDomain k] [UniqueFactorizationMonoid k]

omit [UniqueFactorizationMonoid k] in
theorem residualRelation_irreducible : Irreducible (residualRelation k) := by
  simpa [residualRelation, mul_comm] using
    MvPolynomial.irreducible_mul_X_add (X (0 : Fin 4) : MvPolynomial (Fin 4) k)
      1 1 (X_ne_zero 0) (by simp) (by simp) isRelPrime_one_right

instance residualIdeal_isPrime : (residualIdeal k).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (residualRelation_irreducible k).prime

instance residualRing_isDomain : IsDomain (ResidualRing k) := inferInstance

instance modA_isDomain : IsDomain (ModA k) :=
  Function.Injective.isDomain (modAEquivResidual k).toRingHom (modAEquivResidual k).injective

end Domain

end

end StableCoordinate.DeterminantPrimeA

namespace StableCoordinate.DeterminantRing

variable (k : Type*) [CommRing k] [IsDomain k] [UniqueFactorizationMonoid k]

/-- The first coordinate of the determinant hypersurface is a prime element. -/
theorem a_prime : Prime (a k) := by
  have ha : a k ≠ 0 := Obstruction.cX_ne_zero k 0
  apply (Ideal.span_singleton_prime ha).mp
  exact (Ideal.Quotient.isDomain_iff_prime (DeterminantPrimeA.aIdeal k)).mp
    (DeterminantPrimeA.modA_isDomain k)

end StableCoordinate.DeterminantRing

end OAI
