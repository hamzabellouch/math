import OAI.Algebra.AuslanderReiten.Parameters
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtension
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace ArExplicit

universe u v w

def GorensteinProjective (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∃ P : ChainComplex (ModuleCat.{max u v} R) ℤ,
    (∀ n : ℤ, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
    (∀ n : ℤ,
      LinearMap.range (P.d (n + 1) n).hom =
        LinearMap.ker (P.d n (n - 1)).hom) ∧
    (∀ (n : ℤ) (f : P.X n →ₗ[R] R),
      f.comp (P.d (n + 1) n).hom = 0 →
      ∃ g : P.X (n - 1) →ₗ[R] R, f = g.comp (P.d n (n - 1)).hom) ∧
    Nonempty (M ≃ₗ[R] (P.X 0 ⧸ LinearMap.range (P.d 1 0).hom))

def PositiveExtVanish (R : Type u) [Ring R]
    (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : Prop :=
  ∀ n : ℕ, 0 < n →
    Subsingleton (CategoryTheory.Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R N) n)

def MainConclusions (k : Type u) [Field k]
    (R : Type u) [Ring R] [Algebra k R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module k M]
    [IsScalarTower k R M] : Prop :=
  FiniteDimensional k R ∧
  FiniteDimensional k M ∧
  ¬ Module.Projective R M ∧
  GorensteinProjective R M ∧
  PositiveExtVanish R M M ∧
  PositiveExtVanish R M R ∧
  Nonempty ((R ⧸ Ring.jacobson R) ≃ₐ[k] (Fin 8 → k)) ∧
  (Ring.jacobson R) ^ 4 ≠ ⊥

structure Candidate where
  R : Type
  [ring : Ring R]
  [algebra : Algebra BaseField R]
  M : Type
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  [baseModule : Module BaseField M]
  [tower : IsScalarTower BaseField R M]

attribute [instance] Candidate.ring Candidate.algebra Candidate.addCommGroup
  Candidate.module Candidate.baseModule Candidate.tower

def FullMainTheorem : Prop :=
  ∃ c : Candidate,
    MainConclusions BaseField c.R c.M ∧
    ∀ (E : Type v) [Field E] [Algebra BaseField E],
      letI := scalarExtensionModule BaseField E c.R c.M
      MainConclusions E (E ⊗[BaseField] c.R) (E ⊗[BaseField] c.M)

end ArExplicit

end

end OAI
