import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PureActualCoefficients

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (k:M →+ ℤ) (p:M) (hp:k p=1)
lemma read_pure_scalar_monomial (b m:M) (c:K) :
    readFiber v Ω k p hp m
      (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
        (embed v Ω hΩ k p hp (Torus.monomial v Ω b c)))=
    c*readFiber v Ω k p hp m
      (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
        (embed v Ω hΩ k p hp (Torus.X v Ω b))) := by
  classical
  rw [Torus.X,embed_monomial,embed_monomial,pureAction_monomial,pureAction_monomial,map_one,one_mul]
  change (expandZero ((Finsupp.single (off k p hp b)
    ((RatFunc.C c*centeredScalar v (k b) (complementAlpha k p Ω (off k p hp b)))*
      (pureRatio v (complementAlpha k p Ω (off k p hp b)):RatFunc K)))
      (off k p hp m))).coeff (k m)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)=
    c*((expandZero ((Finsupp.single (off k p hp b)
      (centeredScalar v (k b) (complementAlpha k p Ω (off k p hp b))*
        (pureRatio v (complementAlpha k p Ω (off k p hp b)):RatFunc K)))
      (off k p hp m))).coeff (k m)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K))
  by_cases ho:off k p hp b=off k p hp m
  · simp only [Finsupp.single_apply,ite_eq_left ho]
    rw [mul_assoc,map_mul,expandZero_constant]
    change ((HahnSeries.single 0 c:HahnSeries ℤ K)*_).coeff (k m)*_=c*(_*_)
    rw [HahnSeries.coeff_single_mul,sub_zero,mul_assoc]
  · simp only [Finsupp.single_apply,ite_eq_right ho,map_zero,HahnSeries.coeff_zero,zero_mul,mul_zero]
end
end ElementaryPositivity.RationalFiber
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber
noncomputable section
variable {M:Type*} [AddCommGroup M]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0) (τ:M →+ ℤ)
local instance purePolynomialCoefficientsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance purePolynomialCoefficientsAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance purePolynomialCoefficientsAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hΩ in
lemma actual_pure_polynomial (k:M →+ ℤ) (p:M) (hp:k p=1) (hτ:τ p=1)
    (F:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ (normalizedSimple Ω p) F m=
      readFiber LaurentRay.vUnit Ω k p hp m
        (pureAction LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)
          (embed LaurentRay.vUnit Ω hΩ k p hp F)) := by
  classical
  induction F using Finsupp.induction_linear with
  | zero=>simp [actualPolynomialAdjointCoefficient]
  | add F G hF hG=>rw [actualPolynomialAdjointCoefficient_add,map_add,map_add,map_add,hF,hG]
  | single b c=>
    change actualPolynomialAdjointCoefficient Ω τ (normalizedSimple Ω p)
      (Torus.monomial LaurentRay.vUnit Ω b c) m=_
    rw [actualPolynomialAdjointCoefficient_monomial,actual_pure_monomial Ω hΩ τ k p hp hτ]
    exact (read_pure_scalar_monomial LaurentRay.vUnit Ω hΩ k p hp b m c).symm
include hΩ in
lemma actual_pure_finite (k:M →+ ℤ) (p:M) (hp:k p=1) (hτ:τ p=1)
    (F G:Torus LaurentRay.vUnit Ω)
    (h:embed LaurentRay.vUnit Ω hΩ k p hp G=
      pureAction LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)
        (embed LaurentRay.vUnit Ω hΩ k p hp F)) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ (normalizedSimple Ω p) F m=G m := by
  rw [actual_pure_polynomial Ω hΩ τ k p hp hτ,←h]
  exact readFiber_embedAdd LaurentRay.vUnit Ω k p hp G m
include hΩ in
lemma actual_pure_order_independent (σ:M →+ ℤ) (p:M) (hτ:τ p=1) (hσ:σ p=1)
    (F:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ (normalizedSimple Ω p) F m=
      actualPolynomialAdjointCoefficient Ω σ (normalizedSimple Ω p) F m := by
  rw [actual_pure_polynomial Ω hΩ τ τ p hτ hτ,
    actual_pure_polynomial Ω hΩ σ τ p hτ hσ]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
