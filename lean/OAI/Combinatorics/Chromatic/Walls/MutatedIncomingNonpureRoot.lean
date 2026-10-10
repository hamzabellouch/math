import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutatedIncomingNonpure
import OAI.Combinatorics.Chromatic.Walls.MutatedAnchors

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd : ∀r≠0,∃m,Ω r m≠0)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd in
lemma mutatedIncoming_nonpure_root
    (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    (s:M) (d:ℕ) (hd:0<d) (hs:HasRootDegree (mutatedRoots Ω C pc) d s)
    (hn:¬OnPositiveRay s (simpleRoot (mutatedRoots Ω C pc) pc))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (hA:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      0<realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0) :
    coeff d (FormalLog.log (chartZero LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (incomingCovector Ω s)
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val) s=
    coeff d (FormalLog.log (literalIncomingRay Ω (simpleIncomingList (mutatedRoots Ω C pc)) s)) s := by
  let r:=(mutationIncomingLabelEquiv Ω (simpleRoot C pc) (hΩ _)).symm s
  have hr:mutationIncomingLabel Ω (simpleRoot C pc) r=s:=
    (mutationIncomingLabelEquiv Ω (simpleRoot C pc) (hΩ _)).apply_symm_apply s
  obtain ⟨J,hJ⟩:=mutated_degree_covector Ω C pc e hC
  obtain ⟨hr0,hp,ho⟩:=nonpure_preimage_geometry Ω C pc e he S hS hcomp J hJ r d hd
    (hr.symm ▸ hs) (by rwa [hr])
  have HH:=mutatedIncoming_nonpure Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    r hr0 hp ho (by rwa [hr]) HA HB hA hB d
  simpa only [hr] using HH
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
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
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd in
lemma mutatedIncoming_pure_root
    (s:M) (d:ℕ) (hs:OnPositiveRay s (simpleRoot (mutatedRoots Ω C pc) pc))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:a (e (simpleRoot C pc))<0) (hb:0<b (e (simpleRoot C pc))) :
    coeff d (FormalLog.log (chartZero LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (incomingCovector Ω s)
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val) s=
    coeff d (FormalLog.log (literalIncomingRay Ω (simpleIncomingList (mutatedRoots Ω C pc)) s)) s := by
  let C':=mutatedRoots Ω C pc
  let coord':=mutatedCoordinates Ω C coord pc
  have hc:∀a,coord' (C' a)=a:=mutatedCoordinates_retraction Ω C coord hcoord pc
  have hz:nonpDegree coord' pc s=0:=by
    obtain ⟨a,b,ha,hb,heq⟩:=hs
    have H:=congrArg (nonpDegree coord' pc) heq
    rw [map_nsmul,map_nsmul,nonpDegree_simple_self C' coord' hc pc,nsmul_zero,nsmul_eq_mul] at H
    exact (mul_eq_zero.mp H.symm).resolve_left (by exact_mod_cast (Nat.ne_of_gt hb))
  have hp:incomingCovector Ω s (simpleRoot C' pc)=0:=by
    obtain ⟨a,b,ha,hb,heq⟩:=hs
    have H:=congrArg (Ω (simpleRoot C' pc)) heq
    rw [map_nsmul,map_nsmul,hΩ,nsmul_zero,nsmul_eq_mul] at H
    have HH:(Ω (simpleRoot C' pc)) s=0:=
      (mul_eq_zero.mp H.symm).resolve_left (by exact_mod_cast (Nat.ne_of_gt hb))
    change ((Ω (simpleRoot C' pc)) s:ℝ)=0
    exact_mod_cast HH
  let T:=mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB
  rw [pureFace_log_chart_apply Ω C' coord' hc pc (incomingCovector Ω s) hp T d s hz]
  have HH:=congrArg (fun f:PowerSeries (Torus LaurentRay.vUnit Ω)=>coeff d (FormalLog.log f) s)
    (mutatedTransport_pure Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HB ha hb)
  change coeff d (FormalLog.log (pureFace Ω C' coord' pc T).val) s=_ at HH
  rw [←pureFaceSeries_log Ω C' coord' hc pc,pureFaceSeries_apply,hz,ite_eq_left rfl] at HH
  rw [literalIncomingRay_eq Ω _ hs,literalIncoming_simple Ω C' coord' hc pc]
  exact HH
end
end ElementaryPositivity.QuantumTorus

end

end OAI
