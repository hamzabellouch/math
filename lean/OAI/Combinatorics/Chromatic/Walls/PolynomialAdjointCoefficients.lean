import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutationMonomialAction

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
local instance polynomialAdjointCoefficientsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance polynomialAdjointCoefficientsAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

def actualPolynomialAdjointCoefficient (τ:M →+ ℤ) (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (F:Torus LaurentRay.vUnit Ω) (m:M) : LaurentSeries ℚ :=
  F.sum (fun b c=>c*actualMonomialAdjointCoefficient Ω τ f b m)

lemma actualPolynomialAdjointCoefficient_add (τ:M →+ ℤ) (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (F G:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ f (F+G) m=
      actualPolynomialAdjointCoefficient Ω τ f F m+actualPolynomialAdjointCoefficient Ω τ f G m := by
  exact Finsupp.sum_add_index' (fun _=>zero_mul _) (fun _ _ _=>add_mul _ _ _)

lemma actualPolynomialAdjointCoefficient_monomial (τ:M →+ ℤ)
    (f:PowerSeries (Torus LaurentRay.vUnit Ω)) (b m:M) (c:LaurentSeries ℚ) :
    actualPolynomialAdjointCoefficient Ω τ f (Torus.monomial LaurentRay.vUnit Ω b c) m=
      c*actualMonomialAdjointCoefficient Ω τ f b m := by
  exact Finsupp.sum_single_index (zero_mul _)

include hcoord in
lemma actualPolynomialAdjointCoefficient_push (pos:Bool) (f:CompletedPositive LaurentRay.vUnit Ω C)
    (hf:RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f.val)
    (F:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω (rootOrder (mutatedCoordinates Ω C coord pc))
      (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f.val)
      (mutationTorusPush Ω hΩ C pc pos LaurentRay.vUnit F) (mutationLinearPiece Ω C pc pos m)=
      actualPolynomialAdjointCoefficient Ω (rootOrder coord) f.val F m := by
  induction F using Finsupp.induction_linear with
  | zero=>simp [actualPolynomialAdjointCoefficient]
  | add F G hF hG=>rw [map_add,actualPolynomialAdjointCoefficient_add,
      actualPolynomialAdjointCoefficient_add,hF,hG]
  | single b c=>
    change actualPolynomialAdjointCoefficient Ω _ _
      (mutationTorusPush Ω hΩ C pc pos LaurentRay.vUnit (Torus.monomial LaurentRay.vUnit Ω b c)) _=_
    rw [mutationTorusPush,Torus.push_monomial,actualPolynomialAdjointCoefficient_monomial,
      mutation_actualMonomialAdjointCoefficient Ω hΩ C coord hcoord pc pos f hf]
    exact (actualPolynomialAdjointCoefficient_monomial Ω _ _ b m c).symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
