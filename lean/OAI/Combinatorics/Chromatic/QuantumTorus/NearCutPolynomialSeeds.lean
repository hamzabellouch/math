import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.NearCutSectionCharts
import OAI.Combinatorics.Chromatic.Walls.FinitePureMutation

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
local instance nearCutPolynomialSeedsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance nearCutPolynomialSeedsAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance nearCutPolynomialSeedsAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

def PureInitialRelation (F F':Torus LaurentRay.vUnit Ω) : Prop :=
  embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) F=
    pureAction LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)
        (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) F')

include hcoord in
lemma rootOrder_simple : rootOrder coord (simpleRoot C pc)=1 :=
  rootOrder_eq C coord hcoord (simpleRoot_degree C pc)

include he hdeg hS hcomp in
lemma nearCut_old_positive_seed (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc)))
    (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F') (m:M) :
    polynomialSectionCoefficient Ω C coord (b.toAddMonoidHom.comp e) F m=F' m := by
  unfold polynomialSectionCoefficient
  rw [nearCut_old_section_chart Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hC HA HB ha hb hap hbp]
  apply actualPolynomialAdjoint_inverse_finite Ω hΩ C coord hcoord (simpleCompleted Ω C coord hcoord pc) F' F
  intro x
  exact actual_pure_finite Ω hΩ (rootOrder coord) (pureDegree coord pc) (simpleRoot C pc)
    (pureDegree_simple_self C coord hcoord pc) (rootOrder_simple C coord hcoord pc) F' F hF x

lemma pure_mutated_inverse_finite
    (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F') (m:M) :
    actualPolynomialAdjointCoefficient Ω (rootOrder (mutatedCoordinates Ω C coord pc))
      (invOfUnit (normalizedSimple Ω (-simpleRoot C pc)) 1) F' m=
      mutationTorusPush Ω hΩ C pc false LaurentRay.vUnit F m := by
  let C':=(mutatedRoots Ω C pc)
  let coord':=mutatedCoordinates Ω C coord pc
  have hc:∀d,coord' (C' d)=d:=mutatedCoordinates_retraction Ω C coord hcoord pc
  have hp:rootOrder coord' (-simpleRoot C pc)=1:=by
    rw [←mutatedRoot_p Ω C pc]
    exact rootOrder_simple C' coord' hc pc
  have H:=actualPolynomialAdjoint_inverse_finite Ω hΩ C' coord' hc (simpleCompleted Ω C' coord' hc pc)
    (mutationTorusPush Ω hΩ C pc false LaurentRay.vUnit F) F' ?_ m
  · change actualPolynomialAdjointCoefficient Ω (rootOrder coord')
      (invOfUnit (normalizedSimple Ω (simpleRoot C' pc)) 1) _ m=_ at H
    rw [show simpleRoot C' pc= -simpleRoot C pc from mutatedRoot_p Ω C pc] at H
    exact H
  · intro x
    change actualPolynomialAdjointCoefficient Ω (rootOrder coord') (normalizedSimple Ω (simpleRoot C' pc)) _ x=_
    rw [show simpleRoot C' pc= -simpleRoot C pc from mutatedRoot_p Ω C pc]
    exact finite_cut_actual Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (pureDegree_simple_self C coord hcoord pc) (rootOrder coord') hp F F' hF x

variable (hnd:∀r≠0,∃m,Ω r m≠0)
include he hdeg hS hcomp hnd in
lemma nearCut_new_positive_seed (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc)))
    (ha':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) a (e m)≠0)
    (hb':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) b (e m)≠0)
    (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F') (m:M) :
    polynomialSectionCoefficient Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
      ((realMutationCovector e S (simpleRoot C pc) a).toAddMonoidHom.comp e) F' m=
      mutationTorusPush Ω hΩ C pc false LaurentRay.vUnit F m := by
  unfold polynomialSectionCoefficient
  rw [nearCut_new_section_chart Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC HA HB ha hb hap hbp ha' hb']
  exact pure_mutated_inverse_finite Ω hΩ C coord hcoord pc F F' hF m
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber FiniteRayGeometry
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
local instance nearCutPolynomialMutationRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance nearCutPolynomialMutationAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance nearCutPolynomialMutationAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

include he hdeg hS hcomp hnd in
lemma polynomialSection_mutation (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F')
    (pos:Bool) (h:Module.Dual ℝ E) (HH:RegularCovector C e h)
    (hs:cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc))
    (HH':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) h (e m)≠0) (m:M) :
    polynomialSectionCoefficient Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
      ((realMutationCovector e S (simpleRoot C pc) h).toAddMonoidHom.comp e) F'
        (mutationLinearPiece Ω C pc pos m)=
      polynomialSectionCoefficient Ω C coord (h.toAddMonoidHom.comp e) F m := by
  obtain ⟨a,HA,ha,hap,ha'⟩:=nearCut_double_regular Ω C pc e S hS hC false
  obtain ⟨b,HB,hb,hbp,hb'⟩:=nearCut_double_regular Ω C pc e S hS hC true
  have hc:∀d,mutatedCoordinates Ω C coord pc (mutatedRoots Ω C pc d)=d:=
    mutatedCoordinates_retraction Ω C coord hcoord pc
  have haF:∀x,polynomialSectionCoefficient Ω C coord (a.toAddMonoidHom.comp e) F x=F x:=
    polynomialSection_negative Ω hΩ C coord _ (nearCut_old_negative Ω C pc e ha hap) F
  have hbF:∀x,polynomialSectionCoefficient Ω C coord (b.toAddMonoidHom.comp e) F x=F' x:=
    nearCut_old_positive_seed Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hC HA HB ha hb hap hbp F F' hF
  have haG:∀x,polynomialSectionCoefficient Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
      ((realMutationCovector e S (simpleRoot C pc) a).toAddMonoidHom.comp e) F' x=
      mutationTorusPush Ω hΩ C pc false LaurentRay.vUnit F x:=
    nearCut_new_positive_seed Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC HA HB ha hb hap hbp ha' hb' F F' hF
  have hbG:∀x,polynomialSectionCoefficient Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
      ((realMutationCovector e S (simpleRoot C pc) b).toAddMonoidHom.comp e) F' x=F' x:=by
    intro x
    unfold polynomialSectionCoefficient
    rw [nearCut_new_section_one Ω C pc e S hb hbp,actualPolynomialAdjointCoefficient_one Ω hΩ]
  cases pos
  · rw [polynomialSection_rebase Ω hΩ C coord hcoord (a.toAddMonoidHom.comp e) _ F F haF,
      polynomialSection_rebase Ω hΩ (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc) hc
        ((realMutationCovector e S (simpleRoot C pc) a).toAddMonoidHom.comp e) _ F' _ haG]
    exact halfspace_canonical_polynomial_coefficients Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC
      false HA HH hap hs ha' HH' F m
  · rw [polynomialSection_rebase Ω hΩ C coord hcoord (b.toAddMonoidHom.comp e) _ F F' hbF,
      polynomialSection_rebase Ω hΩ (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc) hc
        ((realMutationCovector e S (simpleRoot C pc) b).toAddMonoidHom.comp e) _ F' F' hbG]
    have H:=halfspace_canonical_polynomial_coefficients Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC
      true HB HH hbp hs hb' HH' F' m
    have hid:mutationTorusPush Ω hΩ C pc true LaurentRay.vUnit F'=F':=by
      apply Finsupp.ext
      intro x
      have HB:=mutationTorusPush_read Ω hΩ C pc true LaurentRay.vUnit F' x
      exact HB
    rwa [hid] at H
end
end ElementaryPositivity.QuantumTorus

end

end OAI
