import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.RingGroupHomology
import OAI.GroupTheory.SimpleAmenable.RandomFields.PeriodizationCovariance

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TorusCoefficientFinite

open Classical
namespace SquareStep

abbrev OrbitGroupRing := MonoidAlgebra ℤ (Multiplicative (ℤ×ℤ))

noncomputable def orbitGroupRing : PolygonGroupRing →+* OrbitGroupRing :=
  MonoidAlgebra.mapDomainRingHom ℤ orbitProjection

noncomputable def periodizeModule {a : ℕ} :
    (PlaneStep.representation a).asModule →ₛₗ[orbitGroupRing]
      (orbitRepresentation a).asModule where
  toFun := periodize
  map_add' := periodize.map_add
  map_smul' r x := by
    change PlaneStep a at x
    change periodize ((PlaneStep.representation a).asAlgebraHom r x) =
      (orbitRepresentation a).asAlgebraHom (orbitGroupRing r) (periodize x)
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r s hr hs => simp [hr,hs]
    | single g c =>
      simp only [orbitGroupRing,MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single,Representation.asAlgebraHom_single,
        LinearMap.smul_apply,map_smul]
      congr 1
      change periodize (PlaneStep.translate g.toAdd x) =
        orbitRepresentation a (orbitProjection g) (periodize x)
      rw [← representation_reduce]
      exact periodize_translate x g.toAdd

theorem periodizeModule_surjective {a : ℕ} :
    Function.Surjective (periodizeModule (a := a)) := periodize_surjective

theorem orbit_coefficient_finite {a : ℕ} (ha : 0<a) :
    Module.Finite OrbitGroupRing (orbitRepresentation a).asModule := by
  let := polygon_coefficient_finite ha
  exact Module.Finite.of_surjective periodizeModule periodizeModule_surjective

instance : IsNoetherianRing OrbitGroupRing := by
  let : Algebra.FiniteType ℤ OrbitGroupRing :=
    MonoidAlgebra.finiteType_iff_group_fg.mpr inferInstance
  exact Algebra.FiniteType.isNoetherianRing ℤ OrbitGroupRing

end SquareStep
end TorusCoefficientFinite

section TensorCoefficientFinite

open scoped TensorProduct
attribute [local instance 1200] Representation.instModuleAsModule TensorProduct.instModule
attribute [local instance 1300] TensorProduct.leftModule
namespace RingCoinvariants

theorem finite_tensor (k R M K : Type*) [CommRing k] [CommRing R] [Algebra k R]
    [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
    [SMulCommClass k R M] [AddCommGroup K] [Module k K]
    [Module.Finite R M] [Module.Finite k K] : Module.Finite R (M ⊗[k] K) := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange k R R M K
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

variable {G M K : Type} [CommGroup G] [AddCommGroup M] [Module ℤ M]
  [AddCommGroup K] [Module ℤ K]
local notation "R" => MonoidAlgebra ℤ G

noncomputable def trivialTensorEquiv (ρ : Representation ℤ G M) :
    (ρ.asModule ⊗[ℤ] K) ≃ₗ[ℤ] (ρ.tprod (Representation.trivial ℤ G K)).asModule :=
  (TensorProduct.congr ρ.asModuleEquiv (LinearEquiv.refl ℤ K)).trans
    (ρ.tprod (Representation.trivial ℤ G K)).asModuleEquiv.symm

noncomputable def trivialTensorMap (ρ : Representation ℤ G M) :
    (ρ.asModule ⊗[ℤ] K) →ₗ[R] (ρ.tprod (Representation.trivial ℤ G K)).asModule :=
  MonoidAlgebra.equivariantOfLinearOfComm (trivialTensorEquiv ρ).toLinearMap (by
    intro g x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [smul_add,map_add,hx,hy]
    | tmul x y =>
      apply (ρ.tprod (Representation.trivial ℤ G K)).asModuleEquiv.injective
      simp [trivialTensorEquiv,TensorProduct.smul_tmul']
      rfl)

theorem finite_trivialTensor (ρ : Representation ℤ G M)
    [Module.Finite R ρ.asModule] [Module.Finite ℤ K] :
    Module.Finite R (ρ.tprod (Representation.trivial ℤ G K)).asModule := by
  let : Module.Finite R (ρ.asModule ⊗[ℤ] K) := finite_tensor ℤ R ρ.asModule K
  exact Module.Finite.of_surjective (trivialTensorMap ρ) (trivialTensorEquiv ρ).surjective

end RingCoinvariants
end TensorCoefficientFinite

section PolygonCoefficientHomology

attribute [local instance 1200] Rep.hV2 Representation.instModuleAsModule TensorProduct.instModule
namespace SquareStep

noncomputable def coefficientRep (a : ℕ) (K : Type) [AddCommGroup K] [Module ℤ K] :
    Rep ℤ (Multiplicative (ℤ×ℤ)) :=
  Rep.of ((orbitRepresentation a).tprod (Representation.trivial ℤ _ K))

theorem coefficient_homology_finite {a : ℕ} (ha : 0<a) (K : Type)
    [AddCommGroup K] [Module ℤ K] [Module.Finite ℤ K] (n : ℕ) :
    Module.Finite ℤ (groupHomology (coefficientRep a K) n) := by
  let : Module.Finite OrbitGroupRing (orbitRepresentation a).asModule :=
    orbit_coefficient_finite ha
  let : Module.Finite OrbitGroupRing (coefficientRep a K).ρ.asModule :=
    RingCoinvariants.finite_trivialTensor (orbitRepresentation a)
  exact RingCoinvariants.finite_groupHomology (coefficientRep a K) n

end SquareStep
end PolygonCoefficientHomology

end SimpleAmenable
end
end

end OAI
