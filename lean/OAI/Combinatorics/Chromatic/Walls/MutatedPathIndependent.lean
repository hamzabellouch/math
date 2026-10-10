import Mathlib
import OAI.Combinatorics.Chromatic.Walls.LaurentCompletionFaithful

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
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
local instance mutatedPathIndependentRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance mutatedPathIndependentAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedPathIndependentAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

include hcoord hS hcomp hnd in
lemma mutatedPathCompletion_independent {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (p q : GenericLinePath C e a b) :
    mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p=
      mutatedPathCompletion Ω hΩ C coord pc e he L hdeg q := by
  obtain ⟨r⟩:=generic_path_exists C e b a HB HA
  have H1:=mutatedPathCompletion_loop Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd (p.trans C e r)
  have H2:=mutatedPathCompletion_loop Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd (r.trans C e q)
  rw [mutatedPathCompletion_trans] at H1 H2
  calc
    _ = 1*mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p := (one_mul _).symm
    _ = (mutatedPathCompletion Ω hΩ C coord pc e he L hdeg q*
        mutatedPathCompletion Ω hΩ C coord pc e he L hdeg r)*
        mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p := by rw [H2]
    _ = mutatedPathCompletion Ω hΩ C coord pc e he L hdeg q*1 := by rw [mul_assoc,H1]
    _ = _ := mul_one _

def mutatedTransport {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) :
    CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
  mutatedPathCompletedPositive Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp
    (Classical.choice (generic_path_exists C e a b HA HB))

include hnd in
lemma mutatedTransport_eq_path {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (p : GenericLinePath C e a b) :
    (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val=
      mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p :=
  mutatedPathCompletion_independent Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HB _ p

include hnd in
lemma mutatedTransport_self {a : Module.Dual ℝ E} (HA : RegularCovector C e a) :
    (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HA).val=1 :=
  mutatedPathCompletion_loop Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd _

include hnd in
lemma mutatedTransport_trans {a b c : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) (HC : RegularCovector C e c) :
    (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HC).val=
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HB HC).val*
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val := by
  let p:=Classical.choice (generic_path_exists C e a b HA HB)
  let q:=Classical.choice (generic_path_exists C e b c HB HC)
  rw [mutatedTransport_eq_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HC (p.trans C e q)]
  exact mutatedPathCompletion_trans Ω hΩ C coord pc e he L hdeg p q
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
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
local instance mutatedPathIndependentPureRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance mutatedPathIndependentPureAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedPathIndependentPureAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hcoord hS hcomp in
omit [FiniteDimensional ℝ E] in
lemma mutatedPathCompletion_pure {a b:Module.Dual ℝ E} (p:GenericLinePath C e a b) :
    pureFaceSeries Ω (mutatedCoordinates Ω C coord pc) pc
      (mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p)*
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<a (e (simpleRoot C pc))))=
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<b (e (simpleRoot C pc)))) := by
  induction p with
  | nil=>rw [mutatedPathCompletion,pureFaceSeries_one,one_mul]
  | append s p ih=>
    rw [mutatedPathCompletion,pureFaceSeries_mul Ω (mutatedRoots Ω C pc)
      (mutatedCoordinates Ω C coord pc) (mutatedCoordinates_retraction Ω C coord hcoord pc) pc _ _
      (mutatedLineCompletion_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
        s.direction s.offset s.generic s.lo s.hi)
      (mutatedPathCompletion_graded Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp p),
      mul_assoc,ih]
    exact mutatedLineCompletion_pure Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi s.ordered (s.start_regular 1) (s.finish_regular 1)

include hnd in
lemma mutatedTransport_pure {a b:Module.Dual ℝ E}
    (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:a (e (simpleRoot C pc))<0) (hb:0<b (e (simpleRoot C pc))) :
    pureFaceSeries Ω (mutatedCoordinates Ω C coord pc) pc
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val=
      normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc) := by
  obtain ⟨p⟩:=generic_path_exists C e a b HA HB
  rw [mutatedTransport_eq_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HB p]
  have HH:=mutatedPathCompletion_pure Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p
  simpa only [pureCutGauge,decide_eq_false (not_lt.mpr (le_of_lt ha)),Bool.false_eq_true,ite_false,
    decide_eq_true hb,ite_true,mul_one] using HH
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)

def GenericLinePath.InRegion (U : Set (Module.Dual ℝ E))
    {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) : Prop :=
  match p with
  | .nil _=>True
  | .append s p=>(∀t,s.lo≤t → t ≤ s.hi → s.offset+t • s.direction∈U) ∧ p.InRegion U

lemma GenericLinePath.InRegion.trans {U : Set (Module.Dual ℝ E)} {a b c : Module.Dual ℝ E}
    {p : GenericLinePath C e a b} {q : GenericLinePath C e b c}
    (hp : p.InRegion C e U) (hq : q.InRegion C e U) :
    (p.trans C e q).InRegion C e U := by
  induction q with
  | nil=>exact hp
  | append s q ih=>exact ⟨hq.1,ih hq.2⟩

lemma GenericLinePath.InRegion.castEnds {U : Set (Module.Dual ℝ E)}
    {a b a' b' : Module.Dual ℝ E} (h0 : a=a') (h1 : b=b')
    {p : GenericLinePath C e a b} (hp : p.InRegion C e U) :
    (p.castEnds C e h0 h1).InRegion C e U := by
  subst a'; subst b'; exact hp

lemma segmentBetween_inRegion {U : Set (Module.Dual ℝ E)} (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 (b-a) a)
    (hU : ∀t:ℝ,0≤t → t≤1 → (1-t) • a+t • b∈U) :
    (GenericLinePath.single C e (segmentBetween C e a b HA HB H)).InRegion C e U := by
  refine ⟨?_,trivial⟩
  intro t hlo hhi
  change a+t • (b-a)∈U
  have heq : a+t • (b-a)=(1-t) • a+t • b := by
    module
  rw [heq]
  exact hU t hlo hhi
end

noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
lemma generic_region_path_via (a b k : Module.Dual ℝ E) (P : Finset E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (U : Set (Module.Dual ℝ E))
    (hU : ∀h : Module.Dual ℝ E,
      (∀x∈P,(0<k x → 0<h x) ∧ (k x<0 → h x<0)) →
      (∀t:ℝ,0≤t → t≤1 → (1-t) • a+t • h∈U) ∧
      (∀t:ℝ,0≤t → t≤1 → (1-t) • h+t • b∈U)) :
    ∃p : GenericLinePath C e a b,p.InRegion C e U := by
  obtain ⟨h,Ha,Hb,HP⟩:=generic_for_two_directions (realRootsThrough e C) a b k P
  have HH : RegularCovector C e h:=by
    intro N s hs hn
    exact (Ha N).avoid s hs (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  let s:=segmentBetween C e a h HA HH (fun N=>(Ha N).join (HA N))
  let t:=segmentBetween C e h b HH HB (fun N=>(Hb N).join_reverse (HB N))
  let p:=(GenericLinePath.single C e s).castEnds C e
    (segmentBetween_start C e a h HA HH _) (segmentBetween_finish C e a h HA HH _)
  let q:=(GenericLinePath.single C e t).castEnds C e
    (segmentBetween_start C e h b HH HB _) (segmentBetween_finish C e h b HH HB _)
  have hp : p.InRegion C e U :=
    (segmentBetween_inRegion C e a h HA HH _ (hU h HP).1).castEnds C e _ _
  have hq : q.InRegion C e U :=
    (segmentBetween_inRegion C e h b HH HB _ (hU h HP).2).castEnds C e _ _
  exact ⟨p.trans C e q,hp.trans C e hq⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
