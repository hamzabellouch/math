import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteModuleOfIntegralAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExteriorScalarDifference

namespace OAI

/-! # Locally algebraic actions of a finitely generated abelian group -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra IsMulCommutative Polynomial

section Scalars
variable {K R M : Type} [Field K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]

def scalarEndRestrict : Module.End R M →ₐ[K] Module.End K M where
  toFun f := f.restrictScalars K
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
end Scalars

section Representation
variable {K Q M : Type} [Field K] [CommGroup Q] [AddCommGroup M] [Module K M]

local instance locallyAlgebraicEndRing (ρ : Representation K Q M) :
    Ring (Module.End K[Q] ρ.asModule) :=
  Module.End.instRing (R := K[Q]) (N₁ := ρ.asModule)

theorem integral_group_action_of_no_free_orbit (ρ : Representation K Q M)
    [Module.Finite K[Q] ρ.asModule]
    (h : ∀ g v, ¬LinearIndependent K (fun i : ℕ => (ρ g ^ i) v)) (g : Q) :
    IsIntegral K (Algebra.lsmul K K ρ.asModule (MonoidAlgebra.of K Q g)) := by
  let T : Module.End K[Q] ρ.asModule :=
    Algebra.lsmul K K[Q] ρ.asModule (MonoidAlgebra.of K Q g)
  have he (v : ρ.asModule) (i : ℕ) :
      ρ.asModuleEquiv (((T.restrictScalars K) ^ i) v) = (ρ g ^ i) (ρ.asModuleEquiv v) := by
    induction i with
    | zero => rfl
    | succ i hi =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      change ρ.asModuleEquiv (MonoidAlgebra.of K Q g • ((T.restrictScalars K) ^ i) v) = _
      rw [Representation.asModuleEquiv_map_smul, MonoidAlgebra.of_apply, Representation.asAlgebraHom_single,
        LinearMap.smul_apply, one_smul, hi]
  have hT : IsIntegral K T := by
    apply integral_endomorphism_of_pointwise_relation
    intro v
    have hdep : ¬LinearIndependent K (fun i : ℕ => ((T.restrictScalars K) ^ i) v) := by
      intro hli
      apply h g (ρ.asModuleEquiv v)
      have hi := hli.map' ρ.asModuleEquiv.toLinearMap
        (LinearMap.ker_eq_bot.mpr ρ.asModuleEquiv.injective)
      simpa only [Function.comp_def, LinearEquiv.coe_coe, he] using hi
    obtain ⟨p, hp, hz⟩ := polynomialOrbit_exists_annihilator (T.restrictScalars K) v hdep
    refine ⟨p, hp, ?_⟩
    have hev := Polynomial.aeval_algHom_apply (scalarEndRestrict (K := K)) T p
    exact (congrArg (fun f : Module.End K ρ.asModule => f v) hev).symm.trans hz
  exact hT.map (scalarEndRestrict (K := K))

theorem finite_representation_of_no_free_orbit (ρ : Representation K Q M)
    [Group.FG Q] [Module.Finite K[Q] ρ.asModule]
    (h : ∀ g v, ¬LinearIndependent K (fun i : ℕ => (ρ g ^ i) v)) :
    FiniteDimensional K M := by
  let φ : K[Q] →ₐ[K] Module.End K ρ.asModule := Algebra.lsmul K K ρ.asModule
  let B := φ.range
  let : IsMulCommutative B := .of_setLike_mul_comm (by
    intro b hb c hc
    obtain ⟨r, rfl⟩ := hb
    obtain ⟨s, rfl⟩ := hc
    rw [← map_mul, mul_comm r s, map_mul])
  have hi : ∀ r : K[Q], IsIntegral K (φ.rangeRestrict r) := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of g =>
      apply (isIntegral_algHom_iff B.val Subtype.val_injective).mp
      exact integral_group_action_of_no_free_orbit ρ h g
    | add r s hr hs =>
      rw [map_add]
      exact @IsIntegral.add K B _ _ _ _ _ hr hs
    | smul c r hr => simpa only [map_smul] using hr.smul c
  have hm : Module.Finite K ρ.asModule := by
    apply finite_module_of_integral_scalar_action (R := K[Q])
    intro r
    exact (hi r).map B.val
  exact Module.Finite.of_surjective ρ.asModuleEquiv.toLinearMap ρ.asModuleEquiv.surjective
end Representation
end PolycyclicRecognition

end

end OAI
