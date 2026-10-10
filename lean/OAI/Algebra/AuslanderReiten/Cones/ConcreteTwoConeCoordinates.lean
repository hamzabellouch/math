import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedMiddleShift
import OAI.Algebra.AuslanderReiten.Cones.TwoConeKoszulCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "τ" => AFrobeniusTrace k q
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
local notation "H" => CohomologyClass (A.simpleComplete q) (A.simpleComplete q)

abbrev twoConeBottomHom (a : ℤ) :=
  evaluatedSimpleObject q ⟶ ((simpleSkeletonTriangle q 0).obj₁)⟦a⟧
abbrev twoConeMiddleHom (a : ℤ) :=
  evaluatedSimpleObject q ⟶ ((simpleSkeletonTriangle q 0).obj₃)⟦a⟧
abbrev twoConeTopHom (a : ℤ) :=
  evaluatedSimpleObject q ⟶ ((simpleTopTriangle q 0).obj₃)⟦a⟧
abbrev twoConeSkeletonHom (a : ℤ) :=
  evaluatedSimpleObject q ⟶ ((simpleSkeletonTriangle q 0).obj₂)⟦a⟧
abbrev twoConeHom (a : ℤ) :=
  evaluatedSimpleObject q ⟶ ((simpleTopTriangle q 0).obj₂)⟦a⟧

def twoConeBottomCoordinate (a : ℤ) : twoConeBottomHom q a ≃ₗ[k] H a :=
  (evaluatedBaseFullHomEquiv q 0 a).trans
    (TateKoszul.degreeEquiv H (by omega))

def twoConeMiddleCoordinate (a : ℤ) : twoConeMiddleHom q a ≃ₗ[k] (H (a-2) × H (a-2)) :=
  evaluatedSingletonFullHomEquiv q 0 a

def twoConeTopCoordinate (a : ℤ) : twoConeTopHom q a ≃ₗ[k] H (a-4) :=
  evaluatedBaseFullHomEquiv q 4 a

def concreteTwoConeFiltration : TwoConeFiltration (k := k)
    (twoConeBottomHom q) (twoConeMiddleHom q) (twoConeTopHom q)
    (twoConeSkeletonHom q) (twoConeHom q) :=
  simpleHomFiltration q 0

end ArExplicit.T

end

end OAI
