import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutatedWallKernel

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
variable (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

lemma pureFaceSeries_of_pure (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf:∀n m,coeff n f m≠0 → nonpDegree coord pc m=0) : pureFaceSeries Ω coord pc f=f := by
  apply PowerSeries.ext
  intro n
  apply Finsupp.ext
  intro m
  rw [pureFaceSeries_apply]
  split_ifs with h
  · rfl
  · exact (not_ne_iff.mp (fun H=>h (hf n m H))).symm

include hcoord in
lemma pureFaceSeries_kernel_one (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf:SeriesGraded LaurentRay.vUnit Ω C f) (hc:constantCoeff f=1)
    (h:M →+ ℝ) (hp:h (simpleRoot C pc)≠0)
    (hk:∀n m,coeff n f m≠0 → h m=0) : pureFaceSeries Ω coord pc f=1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    rw [coeff_pureFaceSeries,coeff_zero_eq_constantCoeff_apply,hc,coeff_zero_eq_constantCoeff_apply,
      constantCoeff_one,zeroProject_one]
  | succ n =>
    apply Finsupp.ext
    intro m
    rw [pureFaceSeries_apply,coeff_one,ite_eq_right (show n+1≠0 by omega)]
    change (if nonpDegree coord pc m=0 then coeff (n+1) f m else 0)=0
    split_ifs with hm
    · by_contra hn
      have hr:HasRootDegree C (n+1) m:=by
        by_contra hh
        exact hn (hf (n+1) m hh)
      have HH:=hk (n+1) m hn
      rw [nonp_zero_root C coord hcoord pc hr hm,map_nsmul,nsmul_eq_mul] at HH
      exact hp ((mul_eq_zero.mp HH).resolve_left (by positivity))
    · rfl

include hcoord in
lemma pureFaceSeries_orient_simple (b:Bool) :
    pureFaceSeries Ω coord pc (orientPowerSeries b (normalizedSimple Ω (simpleRoot C pc)))=
      orientPowerSeries b (normalizedSimple Ω (simpleRoot C pc)) := by
  apply pureFaceSeries_of_pure
  have HH:=orientPowerSeries_submonoid LaurentRay.vUnit Ω
    ((nonpDegree coord pc).ker.toAddSubmonoid) b (normalizedSimple Ω (simpleRoot C pc))
  apply HH
  intro n m hm
  rw [normalizedSimple,coeff_raySeries] at hm
  have heq:m=n • simpleRoot C pc:=by
    by_contra hh
    exact hm (Finsupp.single_eq_of_ne hh)
  change nonpDegree coord pc m=0
  rw [heq,map_nsmul,nonpDegree_simple_self C coord hcoord,nsmul_zero]

variable {E:Type*} [AddCommGroup E] [Module ℝ E]
variable (hΩ:∀m,Ω m m=0) (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k:Module.Dual ℝ E) (H:∀N,GenericOffset (realRootsThrough e C N) 0 v k)

include hcoord hS hcomp in
lemma mutatedLineFactor_pure (a:ℝ) :
    pureFaceSeries Ω (mutatedCoordinates Ω C coord pc) pc
      (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a)=
    if (k+a • v) (e (simpleRoot C pc))=0 then
      orientPowerSeries (!(decide (v (e (simpleRoot C pc))<0)))
        (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc)) else 1 := by
  classical
  by_cases hp:(k+a • v) (e (simpleRoot C pc))=0
  · have hevent:∃N,a∈lineEvents (realRootsThrough e C N) v k:=
      ⟨1,RationalFiber.line_cut_event C pc e L hdeg v k H a hp⟩
    rw [ite_eq_left hp,mutatedLineFactor,dite_eq_left hevent,ite_eq_left hp]
    exact pureFaceSeries_orient_simple Ω (mutatedRoots Ω C pc)
      (mutatedCoordinates Ω C coord pc) (mutatedCoordinates_retraction Ω C coord hcoord pc) pc _
  · rw [ite_eq_right hp]
    apply pureFaceSeries_kernel_one Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
      (mutatedCoordinates_retraction Ω C coord hcoord pc) pc _
      (mutatedLineFactor_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a)
      (mutatedLineFactor_constant Ω hΩ C coord pc e he L hdeg v k H a)
      ((realMutationCovector e S (simpleRoot C pc) (k+a • v)).toAddMonoidHom.comp e)
    · change realMutationCovector e S (simpleRoot C pc) (k+a • v)
        (e (simpleRoot (mutatedRoots Ω C pc) pc))≠0
      rw [mutatedRoot_p,map_neg,map_neg,realMutationCovector_at_p e S _ hS]
      exact neg_ne_zero.mpr hp
    · exact mutatedLineFactor_kernel Ω hΩ C coord pc e he S hS hcomp L hdeg v k H a
end
end ElementaryPositivity.QuantumTorus

end

end OAI
