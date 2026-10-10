import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PureActualCoefficients
import OAI.Combinatorics.Chromatic.QuantumTorus.MutatedSystemIdentification

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)
local instance halfspacePolynomialCoefficientsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance halfspacePolynomialCoefficientsAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

def rootChartRatio (a b:M →+ ℝ) : CompletedPositive LaurentRay.vUnit Ω C :=
  ⟨(chartNegative LaurentRay.vUnit Ω C b (simpleTotalTransport Ω C)).val*
      invOfUnit (chartNegative LaurentRay.vUnit Ω C a (simpleTotalTransport Ω C)).val 1,
    by simp only [map_mul,(chartNegative LaurentRay.vUnit Ω C b (simpleTotalTransport Ω C)).property.1,
      constantCoeff_invOfUnit,inv_one,Units.val_one,mul_one],
    SeriesGraded.mul LaurentRay.vUnit Ω C
      (chartNegative LaurentRay.vUnit Ω C b (simpleTotalTransport Ω C)).property.2
      (SeriesGraded.inverse LaurentRay.vUnit Ω C
        (chartNegative LaurentRay.vUnit Ω C a (simpleTotalTransport Ω C)).property.2)⟩

include hnd hcoord he hS hcomp hdeg in
lemma halfspace_polynomial_coefficients (pos:Bool) {a b:Module.Dual ℝ E}
    (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:cutSide pos (a.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hb:cutSide pos (b.toAddMonoidHom.comp e) (simpleRoot C pc))
    (F:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω (rootOrder (mutatedCoordinates Ω C coord pc))
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val
      (mutationTorusPush Ω hΩ C pc pos LaurentRay.vUnit F) (mutationLinearPiece Ω C pc pos m)=
      actualPolynomialAdjointCoefficient Ω (rootOrder coord)
        (rootChartRatio Ω C (a.toAddMonoidHom.comp e) (b.toAddMonoidHom.comp e)).val F m := by
  obtain ⟨hbound,heq⟩:=mutatedTransport_nocut Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd pos HA HB ha hb
  rw [heq]
  exact actualPolynomialAdjointCoefficient_push Ω hΩ C coord hcoord pc pos
    (rootChartRatio Ω C (a.toAddMonoidHom.comp e) (b.toAddMonoidHom.comp e)) hbound F m

include hnd hcoord he hS hcomp hdeg in
lemma halfspace_canonical_polynomial_coefficients
    (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    (pos:Bool) {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:cutSide pos (a.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hb:cutSide pos (b.toAddMonoidHom.comp e) (simpleRoot C pc))
    (ha':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) a (e m)≠0)
    (hb':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) b (e m)≠0)
    (F:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω (rootOrder (mutatedCoordinates Ω C coord pc))
      (rootChartRatio Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) a).toAddMonoidHom.comp e)
        ((realMutationCovector e S (simpleRoot C pc) b).toAddMonoidHom.comp e)).val
      (mutationTorusPush Ω hΩ C pc pos LaurentRay.vUnit F) (mutationLinearPiece Ω C pc pos m)=
      actualPolynomialAdjointCoefficient Ω (rootOrder coord)
        (rootChartRatio Ω C (a.toAddMonoidHom.comp e) (b.toAddMonoidHom.comp e)).val F m := by
  have H:=halfspace_polynomial_coefficients Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd pos HA HB ha hb F m
  rw [mutatedTransport_canonical Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC HA HB ha' hb'] at H
  exact H
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits HahnSeries
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)
local instance halfspacePolynomialCoefficientsCoeffRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance halfspacePolynomialCoefficientsCoeffAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsCoeffAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance halfspacePolynomialCoefficientsCoeffNonUnitalSemiring : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance halfspacePolynomialCoefficientsCoeffNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring

def rootSectionChart (h:M →+ ℝ) : CompletedPositive LaurentRay.vUnit Ω C :=
  ⟨(chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val*
      invOfUnit (simpleTotalTransport Ω C).val 1,
    by simp only [map_mul,(chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1,
      constantCoeff_invOfUnit,inv_one,Units.val_one,mul_one],
    SeriesGraded.mul LaurentRay.vUnit Ω C
      (chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.2
      (SeriesGraded.inverse LaurentRay.vUnit Ω C (simpleTotalTransport Ω C).property.2)⟩

def polynomialSectionCoefficient (h:M →+ ℝ) (F:Torus LaurentRay.vUnit Ω) (m:M) : LaurentSeries ℚ :=
  actualPolynomialAdjointCoefficient Ω (rootOrder coord) (rootSectionChart Ω C h).val F m

lemma rootSectionChart_negative (h:M →+ ℝ)
    (hh:∀n,0<n → ∀m,HasRootDegree C n m → h m<0) :
    (rootSectionChart Ω C h).val=1 := by
  have H:(chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val=
      (simpleTotalTransport Ω C).val:=by
    apply PowerSeries.ext
    intro n
    apply chartNegative_of_negative_through LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C) n _ n le_rfl
    intro j hj m hm
    exact hh (j+1) (by omega) m (chart_root_of_ne LaurentRay.vUnit Ω C _ _ _ hm)
  dsimp [rootSectionChart]
  rw [H,mul_invOfUnit _ 1 (simpleTotalTransport Ω C).property.1]

lemma rootChartRatio_section (a b:M →+ ℝ) :
    (rootChartRatio Ω C a b).val=
      (rootSectionChart Ω C b).val*invOfUnit (rootSectionChart Ω C a).val 1 := by
  dsimp [rootChartRatio,rootSectionChart]
  rw [inverse_mul _ _ (chartNegative LaurentRay.vUnit Ω C a (simpleTotalTransport Ω C)).property.1 (by simp),
    inverse_inverse _ (simpleTotalTransport Ω C).property.1]
  simp only [mul_assoc]
  rw [←mul_assoc (invOfUnit (simpleTotalTransport Ω C).val 1),
    invOfUnit_mul _ 1 (simpleTotalTransport Ω C).property.1,one_mul]

include hΩ hcoord in
lemma polynomialSection_rebase (a b:M →+ ℝ) (F G:Torus LaurentRay.vUnit Ω)
    (ha:∀m,polynomialSectionCoefficient Ω C coord a F m=G m) (m:M) :
    polynomialSectionCoefficient Ω C coord b F m=
      actualPolynomialAdjointCoefficient Ω (rootOrder coord) (rootChartRatio Ω C a b).val G m := by
  have HA: hahnAction (rootSectionChart Ω C a).val (latticeHahn LaurentRay.vUnit Ω (rootOrder coord) F)=
      latticeHahn LaurentRay.vUnit Ω (rootOrder coord) G:=
    (hahnAction_finite_iff Ω hΩ C coord hcoord (rootSectionChart Ω C a) F G).mpr ha
  have HB: hahnAction (rootChartRatio Ω C a b).val (latticeHahn LaurentRay.vUnit Ω (rootOrder coord) G)=
      hahnAction (rootSectionChart Ω C b).val (latticeHahn LaurentRay.vUnit Ω (rootOrder coord) F):=by
    rw [rootChartRatio_section,hahnAction_mul _ _ _ (rootSectionChart Ω C b).property.1 (by simp),←HA,
      hahnAction_inverse_cancel _ _ (rootSectionChart Ω C a).property.1]
  have H:=congrArg (fun x:HahnSeries ℤ (Torus LaurentRay.vUnit Ω)=>x.coeff (rootOrder coord m) m) HB
  simpa only [hahnAction_actual_coeff Ω hΩ,polynomialSectionCoefficient] using H.symm

omit [DecidableEq I] in
include hΩ hcoord in
lemma actualPolynomialAdjoint_inverse_finite (f:CompletedPositive LaurentRay.vUnit Ω C)
    (F G:Torus LaurentRay.vUnit Ω)
    (h:∀m,actualPolynomialAdjointCoefficient Ω (rootOrder coord) f.val F m=G m) (m:M) :
    actualPolynomialAdjointCoefficient Ω (rootOrder coord) (invOfUnit f.val 1) G m=F m := by
  have H:=(hahnAction_finite_iff Ω hΩ C coord hcoord f F G).mpr h
  have H':=congrArg (hahnAction (invOfUnit f.val 1)) H
  rw [hahnAction_inverse_cancel _ _ f.property.1] at H'
  have HM:=congrArg (fun x:HahnSeries ℤ (Torus LaurentRay.vUnit Ω)=>x.coeff (rootOrder coord m) m) H'
  simpa only [hahnAction_actual_coeff Ω hΩ,latticeHahn_coeff,ite_true] using HM.symm

include hΩ in
lemma actualPolynomialAdjointCoefficient_one (τ:M →+ ℤ) (F:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ 1 F m=F m := by
  rw [←hahnAction_actual_coeff Ω hΩ,hahnAction_one,latticeHahn_coeff,ite_eq_left rfl]

include hΩ in
lemma polynomialSection_negative (h:M →+ ℝ)
    (hh:∀n,0<n → ∀m,HasRootDegree C n m → h m<0)
    (F:Torus LaurentRay.vUnit Ω) (m:M) : polynomialSectionCoefficient Ω C coord h F m=F m := by
  unfold polynomialSectionCoefficient
  rw [rootSectionChart_negative Ω C h hh,actualPolynomialAdjointCoefficient_one Ω hΩ]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
