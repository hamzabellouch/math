import OAI.Algebra.AuslanderReiten.Bar.ModuleBarNativeTwist

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def nativeEndpointBase :
    letI := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
    ModuleCat.of R M ≃ₗ[k] ModuleCat.of R M := by
  letI := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  exact {
    toFun := fun x => e x
    invFun := fun x => e.symm x
    left_inv := fun x => e.symm_apply_apply x
    right_inv := fun x => e.apply_symm_apply x
    map_add' := fun x y => e.map_add x y
    map_smul' := by
      intro a x
      change e ((algebraMap k R a) • x) = (algebraMap k R a) • e x
      rw [he, h.commutes] }

omit [IsScalarTower k R M] [CharP k 2] in
theorem nativeEndpointBase_smul (a : R) (x : ModuleCat.of R M) :
    nativeEndpointBase k R M h e he (a • x) = h a • nativeEndpointBase k R M h e he x :=
  he a x

def nativeTransportBase (n : ℕ) :
    (nativeResolution k R M).complex.X n →ₗ[k] (nativeResolution k R M).complex.X n where
  toFun := transport k R M h e (n+1)
  map_add' := (transport k R M h e (n+1)).map_add
  map_smul' a x := by
    change transport k R M h e (n+1) (left k R M (n+1) (algebraMap k R a) x) =
      left k R M (n+1) (algebraMap k R a) (transport k R M h e (n+1) x)
    erw [transport_left k R M h e he, h.commutes]

theorem nativeTransportBase_smul (n : ℕ) (a : R)
    (x : (nativeResolution k R M).complex.X n) :
    nativeTransportBase k R M h e he n (a • x) =
      h a • nativeTransportBase k R M h e he n x :=
  transport_left k R M h e he (n+1) a x

theorem nativeTransportBase_d (n : ℕ)
    (x : (nativeResolution k R M).complex.X (n+1)) :
    nativeTransportBase k R M h e he n (((nativeResolution k R M).complex.d (n+1) n).hom x) =
      ((nativeResolution k R M).complex.d (n+1) n).hom
        (nativeTransportBase k R M h e he (n+1) x) := by
  change transport k R M h e (n+1) (((complex k R M).d (n+1) n).hom x) =
    ((complex k R M).d (n+1) n).hom (transport k R M h e (n+2) x)
  rw [complex_d]
  exact transport_boundary k R M h e he (n+1) x

def nativeEndpointEquiv : ModuleCat.of R M ≃ₗ[R]
    (ModuleCat.restrictScalars h.toRingHom).obj (ModuleCat.of R M) where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' := he

def nativeEndpointIso : ModuleCat.of R M ≅
    (ModuleCat.restrictScalars h.toRingHom).obj (ModuleCat.of R M) :=
  (nativeEndpointEquiv k R M h e he).toModuleIso

def nativeTransportIso : (nativeResolution k R M).complex ≅
    ((ModuleCat.restrictScalars h.toRingHom).mapHomologicalComplex (.down ℕ)).obj
      (nativeResolution k R M).complex :=
  transportComplexIso k R M h e he

theorem nativeTransport_augmentation :
    (nativeTransportIso k R M h e he).hom.f 0 ≫
        (ModuleCat.restrictScalars h.toRingHom).map ((nativeResolution k R M).π.f 0) =
      (nativeResolution k R M).π.f 0 ≫ (nativeEndpointIso k R M h e he).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (transport_boundary k R M h e he 0 x).symm

theorem nativeTransportBase_π (x : (nativeResolution k R M).complex.X 0) :
    ((nativeResolution k R M).π.f 0).hom (nativeTransportBase k R M h e he 0 x) =
      nativeEndpointBase k R M h e he (((nativeResolution k R M).π.f 0).hom x) :=
  (transport_boundary k R M h e he 0 x).symm

theorem nativeTransport_Hom (n : ℕ)
    (f : (nativeResolution k R M).complex.X n ⟶ ModuleCat.of R M) :
    ModuleCat.ofHom (X := (nativeResolution k R M).complex.X n) (Y := ModuleCat.of R M)
      (show (nativeResolution k R M).complex.X n →ₗ[R] ModuleCat.of R M from
        ((nativeHomTransport k R M h e he).f n).hom f.hom) =
    (nativeTransportIso k R M h e he).hom.f n ≫
      (ModuleCat.restrictScalars h.toRingHom).map f ≫ (nativeEndpointIso k R M h e he).inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end ArExplicit.ModuleBar

end

end OAI
