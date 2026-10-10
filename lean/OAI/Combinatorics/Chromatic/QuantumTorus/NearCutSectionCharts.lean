import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.HalfspacePolynomialCoefficients
import OAI.Combinatorics.Chromatic.Walls.PureCutGroup
import OAI.Combinatorics.Chromatic.QuantumTorus.NearCutMutation

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
local instance nearCutSectionChartsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance nearCutSectionChartsAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance nearCutSectionChartsAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

include hΩ hcoord he hdeg S hS hcomp in
lemma nearCut_old_section_chart (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc))) :
    (rootSectionChart Ω C (b.toAddMonoidHom.comp e)).val=
      invOfUnit (normalizedSimple Ω (simpleRoot C pc)) 1 := by
  have H:=nearCut_chart_ratio Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hC HA HB ha hb hap hbp
  have HH:=congrArg (fun u:(biSupportedSubring LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc))ˣ=>u.val.val) H
  change (rootChartRatio Ω C (a.toAddMonoidHom.comp e) (b.toAddMonoidHom.comp e)).val=
    raySeries LaurentRay.vUnit Ω (simpleRoot C pc) (shiftedElementary LaurentRay.vUnit 0)⁻¹ at HH
  rw [laurent_shiftedElementary_zero,←normalizedSimple_inverse Ω hΩ] at HH
  rw [rootChartRatio_section,rootSectionChart_negative Ω C (a.toAddMonoidHom.comp e) (nearCut_old_negative Ω C pc e ha hap)] at HH
  have hi:invOfUnit (1:PowerSeries (Torus LaurentRay.vUnit Ω)) 1=1:=by
    simpa using mul_invOfUnit (1:PowerSeries (Torus LaurentRay.vUnit Ω)) 1 (by simp)
  simpa only [hi,mul_one] using HH

omit [FiniteDimensional ℝ E] in
lemma nearCut_new_section_one {b:Module.Dual ℝ E} (hb:NearCut Ω C pc e b)
    (hbp:0<b (e (simpleRoot C pc))) :
    (rootSectionChart Ω (mutatedRoots Ω C pc)
      ((realMutationCovector e S (simpleRoot C pc) b).toAddMonoidHom.comp e)).val=1 := by
  rw [realMutationCovector,ite_eq_left hbp.le]
  exact rootSectionChart_negative Ω _ _ (nearCut_new_negative Ω C pc e hb hbp)

variable (hnd:∀r≠0,∃m,Ω r m≠0)
include hΩ hcoord he hdeg hS hcomp hnd in
lemma nearCut_new_section_chart (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc)))
    (ha':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) a (e m)≠0)
    (hb':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) b (e m)≠0) :
    (rootSectionChart Ω (mutatedRoots Ω C pc)
      ((realMutationCovector e S (simpleRoot C pc) a).toAddMonoidHom.comp e)).val=
      invOfUnit (normalizedSimple Ω (-simpleRoot C pc)) 1 := by
  have H:=nearCut_mutated_transport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC HA HB ha hb hap hbp
  rw [mutatedTransport_canonical Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC HA HB ha' hb'] at H
  change (rootChartRatio Ω (mutatedRoots Ω C pc)
    ((realMutationCovector e S (simpleRoot C pc) a).toAddMonoidHom.comp e)
    ((realMutationCovector e S (simpleRoot C pc) b).toAddMonoidHom.comp e)).val=_ at H
  rw [rootChartRatio_section,nearCut_new_section_one Ω C pc e S hb hbp,one_mul,mutatedRoot_p] at H
  have HH:=congrArg (fun f:PowerSeries (Torus LaurentRay.vUnit Ω)=>invOfUnit f 1) H
  rwa [inverse_inverse _ (rootSectionChart Ω _ _).property.1] at HH
end
end ElementaryPositivity.QuantumTorus

end

end OAI
