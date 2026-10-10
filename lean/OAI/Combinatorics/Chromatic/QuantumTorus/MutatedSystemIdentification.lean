import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutatedIncomingNonpureRoot

namespace OAI

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
include hnd in
lemma mutatedTransport_eq_simple
    (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (hA:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      0<realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0) :
    mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB=
      simpleTotalTransport Ω (mutatedRoots Ω C pc) := by
  let C':=mutatedRoots Ω C pc
  have ha:a (e (simpleRoot C pc))<0:=by
    have H:=hA 1 (by omega) _ (simpleRoot_degree C' pc)
    rw [mutatedRoot_p,map_neg,map_neg,realMutationCovector_at_p e S _ hS a] at H
    exact neg_pos.mp H
  have hb:0<b (e (simpleRoot C pc)):=by
    have H:=hB 1 (by omega) _ (simpleRoot_degree C' pc)
    rw [mutatedRoot_p,map_neg,map_neg,realMutationCovector_at_p e S _ hS b] at H
    exact neg_neg_iff_pos.mp H
  let T:=mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB
  have hT:∀n,incomingCoefficient LaurentRay.vUnit Ω C' (n+1) T.val=
      literalIncomingLog Ω C' (simpleIncomingList C') (n+1):=by
    intro n
    apply Finsupp.ext
    intro m
    rw [incomingCoefficient_apply,literalIncomingLog_apply]
    by_cases hm:HasRootDegree C' (n+1) m
    · rw [ite_eq_left hm,ite_eq_left hm]
      change coeff (n+1) (FormalLog.log (chartZero LaurentRay.vUnit Ω C'
        (incomingCovector Ω m) T).val) m=_
      by_cases hp:OnPositiveRay m (simpleRoot C' pc)
      · exact mutatedIncoming_pure_root Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
          m (n+1) hp HA HB ha hb
      · exact mutatedIncoming_nonpure_root Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
          hC m (n+1) (by omega) hm hp HA HB hA hB
    · rw [ite_eq_right hm,ite_eq_right hm]
  exact (existsUnique_incoming LaurentRay.vUnit Ω C' hΩ
    (literalIncomingLog Ω C' (simpleIncomingList C'))
    (literalIncomingLog_graded Ω C' (simpleIncomingList C'))).unique hT
    (incomingSolution_prescription LaurentRay.vUnit Ω C' hΩ _
      (literalIncomingLog_graded Ω C' (simpleIncomingList C')))
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
lemma mutatedTransport_canonical_finite
    (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) (N:ℕ)
    {x y:Module.Dual ℝ E} (HX:RegularCovector C e x) (HY:RegularCovector C e y)
    (hx:∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) x (e m)≠0)
    (hy:∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) y (e m)≠0) :
    ∀n≤N,coeff n (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HX HY).val=
      coeff n ((chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) y).toAddMonoidHom.comp e)
        (simpleTotalTransport Ω (mutatedRoots Ω C pc))).val *
        invOfUnit (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e)
        (simpleTotalTransport Ω (mutatedRoots Ω C pc))).val 1) := by
  obtain ⟨a,b,HA,HB,hA,hB⟩:=mutated_regular_anchors Ω C pc e S hS hC
  have H:=mutatedTransport_negative_ratio Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    N HA HB HX HY (fun n _ m hm=>hA _ (by omega) m hm)
    (fun n _ m hm=>hB _ (by omega) m hm) hx hy
  rw [mutatedTransport_eq_simple Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC HA HB hA hB] at H
  exact H
include hnd in
lemma mutatedTransport_canonical
    (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {x y:Module.Dual ℝ E} (HX:RegularCovector C e x) (HY:RegularCovector C e y)
    (hx:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) x (e m)≠0)
    (hy:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) y (e m)≠0) :
    (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HX HY).val=
      (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) y).toAddMonoidHom.comp e)
        (simpleTotalTransport Ω (mutatedRoots Ω C pc))).val *
        invOfUnit (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e)
        (simpleTotalTransport Ω (mutatedRoots Ω C pc))).val 1 := by
  apply PowerSeries.ext
  intro n
  exact mutatedTransport_canonical_finite Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    hC n HX HY (fun j _ m hm=>hx _ (by omega) m hm)
    (fun j _ m hm=>hy _ (by omega) m hm) n le_rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
