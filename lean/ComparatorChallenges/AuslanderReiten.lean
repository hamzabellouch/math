import Mathlib

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.Statement
universe u v

abbrev K := FractionRing (MvPolynomial (Fin 3) (ZMod 2))

def parameters (i : Fin 3) : K :=
  algebraMap (MvPolynomial (Fin 3) (ZMod 2)) K (MvPolynomial.X i)

def TotallyAcyclicWitness (R : Type u) [Ring R]
    (Z : Type u) [AddCommGroup Z] [Module R Z] : Prop :=
  ∃ P : ChainComplex (ModuleCat.{u} R) ℤ,
    (∀ i : ℤ, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) ∧
    (∀ i : ℤ, LinearMap.range (P.d (i+1) i).hom = LinearMap.ker (P.d i (i-1)).hom) ∧
    (∀ (Q : Type u) [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
      (i : ℤ) (f : P.X i →ₗ[R] Q), f.comp (P.d (i+1) i).hom = 0 →
        ∃ g : P.X (i-1) →ₗ[R] Q, f = g.comp (P.d i (i-1)).hom) ∧
    Nonempty (Z ≃ₗ[R] (P.X 0 ⧸ LinearMap.range (P.d 1 0).hom))

def Conclusions (F R Z : Type u) [Field F] [Ring R] [Algebra F R]
    [AddCommGroup Z] [Module R Z] [Module F Z] [IsScalarTower F R Z] : Prop :=
  FiniteDimensional F R ∧
  FiniteDimensional F Z ∧
  ¬ Module.Projective R Z ∧
  TotallyAcyclicWitness R Z ∧
  (∀ i : ℕ, 0 < i →
    Subsingleton (Abelian.Ext (ModuleCat.of R Z) (ModuleCat.of R Z) i)) ∧
  (∀ i : ℕ, 0 < i →
    Subsingleton (Abelian.Ext (ModuleCat.of R Z) (ModuleCat.of R R) i)) ∧
  Nonempty ((R ⧸ Ring.jacobson R) ≃ₐ[F] (Fin 8 → F)) ∧
  (Ring.jacobson R)^4 ≠ ⊥

structure System where
  algebraCarrier : Type
  [ring : Ring algebraCarrier]
  [scalarAlgebra : Algebra K algebraCarrier]
  moduleCarrier : Type
  [additiveGroup : AddCommGroup moduleCarrier]
  [action : Module algebraCarrier moduleCarrier]
  [scalarAction : Module K moduleCarrier]
  [actionTower : IsScalarTower K algebraCarrier moduleCarrier]

attribute [instance] System.ring System.scalarAlgebra System.additiveGroup
  System.action System.scalarAction System.actionTower

def FullStatement : Prop :=
  AlgebraicIndependent (ZMod 2) parameters ∧
  ∃ s : System,
    Conclusions K s.algebraCarrier s.moduleCarrier ∧
    ∀ (E : Type v) [Field E] [Algebra K E],
      ∃ action : Module (E ⊗[K] s.algebraCarrier) (E ⊗[K] s.moduleCarrier),
      letI := action
      ∃ tower : IsScalarTower E (E ⊗[K] s.algebraCarrier) (E ⊗[K] s.moduleCarrier),
      letI := tower
      (∀ (a b : E) (r : s.algebraCarrier) (z : s.moduleCarrier),
        (a ⊗ₜ[K] r) • (b ⊗ₜ[K] z) = (a*b) ⊗ₜ[K] (r • z)) ∧
      Conclusions E (E ⊗[K] s.algebraCarrier) (E ⊗[K] s.moduleCarrier)

end ArExplicit.Statement

namespace ArExplicit.Statement
universe v

theorem main : FullStatement.{v} := by
  sorry

end ArExplicit.Statement

end

end OAI
