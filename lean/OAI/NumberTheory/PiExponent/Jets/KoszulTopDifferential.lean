import OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone
import OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopTerm

namespace OAI

noncomputable section
universe u
namespace PiExponentSiegelAux.W31
open Module
variable {R : Type u} [CommRing R]

def topDualCoordinate {T : Type u} [AddCommGroup T] [Module R T]
    (e : T ≃ₗ[R] R) : Module.Dual R T ≃ₗ[R] R :=
  e.dualMap.symm.trans (LinearMap.ringLmapEquivSelf R R R)

@[simp] theorem topDualCoordinate_apply {T : Type u} [AddCommGroup T] [Module R T]
    (e : T ≃ₗ[R] R) (φ : Module.Dual R T) :
    topDualCoordinate e φ = φ (e.symm 1) := rfl

def scalarConeTopDualCoordinate (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (r : R) (d : ℕ) (hbound : ∀ n, d < n → Subsingleton (C.X n))
    (e : C.X d ≃ₗ[R] R) :
    Module.Dual R ((W30.scalarConeComplex C r).X (d + 1)) ≃ₗ[R] R :=
  topDualCoordinate ((scalarConeTopEquiv C r d hbound).trans e)

@[simp] theorem scalarConeTopDualCoordinate_apply
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (d : ℕ)
    (hbound : ∀ n, d < n → Subsingleton (C.X n)) (e : C.X d ≃ₗ[R] R)
    (φ : Module.Dual R ((W30.scalarConeComplex C r).X (d + 1))) :
    scalarConeTopDualCoordinate C r d hbound e φ = φ (0, e.symm 1) := rfl

theorem scalarConeTopBoundary_eval (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (r : R) (n : ℕ) (α : Module.Dual R (C.X (n + 1)))
    (β : Module.Dual R (C.X n)) (t : C.X (n + 1)) :
    (((W30.scalarConeComplex C r).d (n + 2) (n + 1)).hom.dualMap (α.coprod β)) (0, t) =
      r * α t - ((C.d (n + 1) n).hom.dualMap β) t := by
  have hd : (W30.scalarConeComplex C r).d (n + 2) (n + 1) =
      W30.scalarConeMap C r (n + 1) :=
    ChainComplex.of_d _ _ (n + 1)
  rw [hd]
  change α ((C.d (n + 2) (n + 1)).hom 0 + r • t) +
      β (-((C.d (n + 1) n).hom t)) = r * α t - β ((C.d (n + 1) n).hom t)
  simp only [map_zero, zero_add, map_smul, map_neg, smul_eq_mul, sub_eq_add_neg]

theorem scalarConeTopDualCoordinate_boundary
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ)
    (hbound : ∀ k, n + 1 < k → Subsingleton (C.X k))
    (e : C.X (n + 1) ≃ₗ[R] R)
    (α : Module.Dual R (C.X (n + 1))) (β : Module.Dual R (C.X n)) :
    scalarConeTopDualCoordinate C r (n + 1) hbound e
      (((W30.scalarConeComplex C r).d (n + 2) (n + 1)).hom.dualMap (α.coprod β)) =
      r * topDualCoordinate e α -
        topDualCoordinate e ((C.d (n + 1) n).hom.dualMap β) := by
  rw [scalarConeTopDualCoordinate_apply]
  exact scalarConeTopBoundary_eval C r n α β (e.symm 1)

theorem scalarConeFirstTopBoundary_eval
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (α : Module.Dual R (C.X 0)) (t : C.X 0) :
    (((W30.scalarConeComplex C r).d 1 0).hom.dualMap α) (0, t) = r * α t := by
  change α ((C.d 1 0).hom 0 + r • t) = r * α t
  simp only [map_zero, zero_add, map_smul, smul_eq_mul]

end PiExponentSiegelAux.W31

end

end OAI
