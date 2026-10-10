import OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom
import OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualEndpoint

namespace OAI

namespace PiExponentSiegelAux.W30
open Module
universe u
variable {R : Type u} [CommRing R]

theorem chain_dual_comp_zero (P : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (P.d (n + 2) (n + 1)).hom.dualMap.comp (P.d (n + 1) n).hom.dualMap = 0 := by
  apply LinearMap.ext
  intro α
  apply LinearMap.ext
  intro x
  change α ((P.d (n + 1) n).hom ((P.d (n + 2) (n + 1)).hom x)) = 0
  have hz : (P.d (n + 1) n).hom ((P.d (n + 2) (n + 1)).hom x) = 0 :=
    LinearMap.congr_fun (chain_linear_comp_zero P n) x
  rw [hz, map_zero]

theorem scalarCone_dual_endpoint_exact
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ)
    (π : Dual R (P.X (n + 2)) →ₗ[R] Q)
    (hlo : LinearMap.range (P.d (n + 1) n).hom.dualMap =
      LinearMap.ker (P.d (n + 2) (n + 1)).hom.dualMap)
    (hπ : LinearMap.range (P.d (n + 2) (n + 1)).hom.dualMap = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    LinearMap.range ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap)
    (((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap)
    (dualConeDifferential (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r)
    (dualConeDifferential (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r)
    (dualProdDualEquivDual R (P.X (n + 1)) (P.X n))
    (dualProdDualEquivDual R (P.X (n + 2)) (P.X (n + 1)))
    (dualProdDualEquivDual R (P.X (n + 3)) (P.X (n + 2)))
  · have hd : (scalarConeComplex P r).d (n + 2) (n + 1) = scalarConeMap P r (n + 1) :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) (n + 1)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r
  · have hd : (scalarConeComplex P r).d (n + 3) (n + 2) = scalarConeMap P r (n + 2) :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) (n + 2)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r
  · exact dualCone_endpoint_exact _ _ _ r π
      (chain_dual_comp_zero P (n + 1)) (chain_dual_comp_zero P n) hlo hπ hr

theorem scalarCone_dual_one_endpoint_exact
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (π : Dual R (P.X 1) →ₗ[R] Q)
    (hπ : LinearMap.range (P.d 1 0).hom.dualMap = LinearMap.ker π)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap)
    (hr : IsSMulRegular Q r) :
    LinearMap.range ((scalarConeComplex P r).d 1 0).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d 2 1).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d 1 0).hom.dualMap)
    (((scalarConeComplex P r).d 2 1).hom.dualMap)
    (dualConeBottom (P.d 1 0).hom r)
    (dualConeDifferential (P.d 2 1).hom (P.d 1 0).hom r)
    (LinearEquiv.refl R (Dual R (P.X 0)))
    (dualProdDualEquivDual R (P.X 1) (P.X 0))
    (dualProdDualEquivDual R (P.X 2) (P.X 1))
  · have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
    rw [hd]
    exact coneBottom_dual_equiv (P.d 1 0).hom r
  · have hd : (scalarConeComplex P r).d 2 1 = scalarConeMap P r 1 :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 1
    rw [hd]
    exact coneDifferential_dual_equiv (P.d 2 1).hom (P.d 1 0).hom r
  · exact dualConeBottom_endpoint_exact _ _ r π (chain_dual_comp_zero P 0) hπ hinj hr

theorem scalarCone_dual_low_exact
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ)
    (π : Dual R (P.X (n + 1)) →ₗ[R] Q)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap)
    (hlow : ∀ k, k < n → LinearMap.range (P.d (k + 1) k).hom.dualMap =
      LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap)
    (hπ : LinearMap.range (P.d (n + 1) n).hom.dualMap = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    ∀ k, k < n + 1 →
      LinearMap.range ((scalarConeComplex P r).d (k + 1) k).hom.dualMap =
        LinearMap.ker ((scalarConeComplex P r).d (k + 2) (k + 1)).hom.dualMap := by
  intro k hk
  by_cases hkn : k < n
  · cases k with
    | zero => exact scalarCone_dual_one_exact P r (hlow 0 hkn) hinj
    | succ k =>
      exact scalarCone_dual_interior_exact P r k (hlow k (by omega))
        (hlow (k + 1) hkn)
  · have hkn : k = n := by omega
    subst k
    cases n with
    | zero => exact scalarCone_dual_one_endpoint_exact P r π hπ hinj hr
    | succ n =>
      exact scalarCone_dual_endpoint_exact P r n π (hlow n (by omega)) hπ hr

end PiExponentSiegelAux.W30

end OAI
