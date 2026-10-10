import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarHigherExteriorNaturality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianNormalExteriorFiniteness

namespace OAI

/-! # FP-infinity controls every rational exterior power of an abelian kernel

The quotient acts by actual conjugation. The surjective map from homology
transfers finite generation to the higher exterior powers.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct MonoidAlgebra IsMulCommutative
attribute [local instance 2000] Rep.hV2 Rep.instLinear

def higherExteriorRepresentation {K Q M : Type} [Field K] [Monoid Q]
    [AddCommGroup M] [Module K M] (ρ : Representation K Q M) (n : ℕ) :
    Representation K Q (⋀[K]^n M) where
  toFun q := exteriorPower.map n (ρ q)
  map_one' := by rw [map_one]; exact exteriorPower.map_id
  map_mul' q r := by rw [map_mul]; exact exteriorPower.map_comp _ _

variable (K : Type) [Field K] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal] [IsMulCommutative N]

def scalarNormalHomology (n : ℕ) : Rep K (G ⧸ N) :=
  Rep.of (scalarExtendedRepresentation K (quotientHomologyAction N (trivialIntegral G) n).ρ)

def scalarAbelianNormalExterior (n : ℕ) : Rep K (G ⧸ N) :=
  Rep.of (higherExteriorRepresentation
    (scalarExtendedRepresentation K (abelianKernelQuotientConjugationAction N)) n)

def scalarAbelianNormalExteriorMap (n : ℕ) :
    scalarNormalHomology K N n ⟶ scalarAbelianNormalExterior K N n := by
  refine Rep.ofHom ⟨scalarHomologyExterior K N n, ?_⟩
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact scalarHomologyExterior_natural K (MulAut.conjNormal (H := N) g).toMonoidHom n

theorem typeFPInfinity_abelianNormalHigherExterior_finite_of_factorial_ne_zero [Group.FG G]
    [IsMulCommutative (G ⧸ N)] (h : TypeFPInfinity G) (n : ℕ)
    (hn : ((n + 1).factorial : K) ≠ 0) :
    Module.Finite K[G ⧸ N] (scalarAbelianNormalExterior K N (n + 1)).ρ.asModule := by
  let A := scalarNormalHomology K N (n + 1)
  let B := scalarAbelianNormalExterior K N (n + 1)
  let : Module.Finite ℤ[G ⧸ N]
      (quotientHomologyAction N (trivialIntegral G) (n + 1)).ρ.asModule :=
    typeFPInfinity_normalHomologyQuotient_finite N h (n + 1)
  let : Module.Finite K[G ⧸ N] A.ρ.asModule :=
    scalarExtendedRepresentation_finite K
      (quotientHomologyAction N (trivialIntegral G) (n + 1)).ρ
  let f := scalarAbelianNormalExteriorMap K N (n + 1)
  let fM : A.ρ.asModule →ₗ[K[G ⧸ N]] B.ρ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule A.ρ B.ρ f.hom
  apply Module.Finite.of_surjective fM
  intro y
  obtain ⟨x, hx⟩ := scalarHomologyExterior_surjective_of_factorial_ne_zero K N n hn (B.ρ.asModuleEquiv y)
  refine ⟨A.ρ.asModuleEquiv.symm x, ?_⟩
  apply B.ρ.asModuleEquiv.injective
  change scalarHomologyExterior K N (n + 1)
    (A.ρ.asModuleEquiv (A.ρ.asModuleEquiv.symm x)) = B.ρ.asModuleEquiv y
  exact (congrArg (scalarHomologyExterior K N (n + 1))
    (A.ρ.asModuleEquiv.apply_symm_apply x)).trans hx

theorem typeFPInfinity_abelianNormalHigherExterior_finite [CharZero K] [Group.FG G]
    [IsMulCommutative (G ⧸ N)] (h : TypeFPInfinity G) (n : ℕ) :
    Module.Finite K[G ⧸ N] (scalarAbelianNormalExterior K N (n + 1)).ρ.asModule :=
  typeFPInfinity_abelianNormalHigherExterior_finite_of_factorial_ne_zero K N h n
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

end PolycyclicRecognition

end

end OAI
