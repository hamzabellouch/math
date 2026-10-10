import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutatedNoCutTransport
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutatedNoCutCone

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
section Algebra
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (pc : I) (e : M →+ E)
omit [Fintype I] in
lemma cutSide_affineSegment (pos : Bool) (a b : Module.Dual ℝ E)
    (ha : cutSide pos (a.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hb : cutSide pos (b.toAddMonoidHom.comp e) (simpleRoot C pc))
    (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    cutSide pos ((a+t • (b-a)).toAddMonoidHom.comp e) (simpleRoot C pc) := by
  cases pos
  · change a (e (simpleRoot C pc))<0 at ha
    change b (e (simpleRoot C pc))<0 at hb
    change (a+t • (b-a)) (e (simpleRoot C pc))<0
    simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply,smul_eq_mul]
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ht1) ha,mul_neg_of_pos_of_neg ht hb]
  · change 0<a (e (simpleRoot C pc)) at ha
    change 0<b (e (simpleRoot C pc)) at hb
    change 0<(a+t • (b-a)) (e (simpleRoot C pc))
    simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply,smul_eq_mul]
    nlinarith [mul_pos (sub_pos.mpr ht1) ha,mul_pos ht hb]

lemma GenericLinePath.OnCutSide.trans {a b c : Module.Dual ℝ E} (pos : Bool)
    (p : GenericLinePath C e a b) (q : GenericLinePath C e b c)
    (hp : p.OnCutSide C pc e pos) (hq : q.OnCutSide C pc e pos) :
    (p.trans C e q).OnCutSide C pc e pos := by
  induction q with
  | nil=>exact hp
  | append s q ih=>exact ⟨hq.1,ih hq.2⟩

lemma GenericLinePath.OnCutSide.reindex {a b a' b' : Module.Dual ℝ E} (pos : Bool)
    (p : GenericLinePath C e a b) (hp : p.OnCutSide C pc e pos) (ha : a=a') (hb : b=b') :
    ∃q : GenericLinePath C e a' b',q.OnCutSide C pc e pos := by
  cases ha
  cases hb
  exact ⟨p,hp⟩

lemma segmentBetween_onCutSide (pos : Bool) (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 (b-a) a)
    (ha : cutSide pos (a.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hb : cutSide pos (b.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    (GenericLinePath.single C e (segmentBetween C e a b HA HB H)).OnCutSide C pc e pos := by
  refine ⟨?_,trivial⟩
  intro t ht ht1
  exact cutSide_affineSegment C pc e pos a b ha hb t ht ht1
end Algebra
section Existence
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (pc : I) (e : M →+ E)
theorem generic_path_exists_onCutSide (pos : Bool) (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (ha : cutSide pos (a.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hb : cutSide pos (b.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    ∃p : GenericLinePath C e a b,p.OnCutSide C pc e pos := by
  classical
  obtain ⟨h,Ha,Hb,HP⟩:=generic_for_two_directions (realRootsThrough e C) a b a {e (simpleRoot C pc)}
  have HH : RegularCovector C e h:=by
    intro N s hs hn
    exact (Ha N).avoid s hs (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  have hs : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc):=by
    have ht:=HP (e (simpleRoot C pc)) (Finset.mem_singleton_self _)
    cases pos
    · exact ht.2 ha
    · exact ht.1 ha
  have hx : ∃p : GenericLinePath C e a h,p.OnCutSide C pc e pos := by
    let s:=segmentBetween C e a h HA HH (fun N=>(Ha N).join (HA N))
    have hh:=segmentBetween_onCutSide C pc e pos a h HA HH (fun N=>(Ha N).join (HA N)) ha hs
    have hp : ∃p : GenericLinePath C e (s.start C e) (s.finish C e),p.OnCutSide C pc e pos:=
      ⟨GenericLinePath.single C e s,hh⟩
    obtain ⟨p,hp⟩:=hp
    exact GenericLinePath.OnCutSide.reindex C pc e pos p hp
      (segmentBetween_start C e _ _ _ _ _) (segmentBetween_finish C e _ _ _ _ _)
  have hy : ∃p : GenericLinePath C e h b,p.OnCutSide C pc e pos := by
    let s:=segmentBetween C e h b HH HB (fun N=>(Hb N).join_reverse (HB N))
    have hh:=segmentBetween_onCutSide C pc e pos h b HH HB (fun N=>(Hb N).join_reverse (HB N)) hs hb
    have hp : ∃p : GenericLinePath C e (s.start C e) (s.finish C e),p.OnCutSide C pc e pos:=
      ⟨GenericLinePath.single C e s,hh⟩
    obtain ⟨p,hp⟩:=hp
    exact GenericLinePath.OnCutSide.reindex C pc e pos p hp
      (segmentBetween_start C e _ _ _ _ _) (segmentBetween_finish C e _ _ _ _ _)
  obtain ⟨p,hp⟩:=hx
  obtain ⟨q,hq⟩:=hy
  exact ⟨p.trans C e q,GenericLinePath.OnCutSide.trans C pc e pos p q hp hq⟩
end Existence
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance mutatedHalfspaceTransportRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance mutatedHalfspaceTransportAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedHalfspaceTransportAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

def endpointRatioPositive (a b : Module.Dual ℝ E) : CompletedPositive LaurentRay.vUnit Ω C := by
  let A:=chartNegative LaurentRay.vUnit Ω C (a.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)
  let B:=chartNegative LaurentRay.vUnit Ω C (b.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)
  refine ⟨(negativeCovectorUnit Ω C coord hcoord pc e b*
    (negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹).val.val,?_,?_⟩
  · change constantCoeff (B.val*(completedInverse LaurentRay.vUnit Ω C A).val)=1
    rw [map_mul,B.property.1,(completedInverse LaurentRay.vUnit Ω C A).property.1,mul_one]
  · exact SeriesGraded.mul LaurentRay.vUnit Ω C B.property.2
      (completedInverse LaurentRay.vUnit Ω C A).property.2

include hΩ he hS hcomp hdeg in
lemma endpointRatioPositive_nocut_cone {a b : Module.Dual ℝ E} (pos : Bool)
    (p : GenericLinePath C e a b) (hs : p.OnCutSide C pc e pos) :
    ∀n m,coeff n (endpointRatioPositive Ω C coord hcoord pc e a b).val m≠0 →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
  change ∀n m,coeff n (negativeCovectorUnit Ω C coord hcoord pc e b*
    (negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹).val.val m≠0 → _
  induction p with
  | nil=>
    simp only [mul_inv_cancel]
    exact series_support_addSubmonoid_one LaurentRay.vUnit Ω _
  | append s p ih=>
    obtain ⟨hs,ht⟩:=hs
    have hp:=ih ht
    have hb:=noncutEndpointRatio_cone Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic pos s.lo s.hi s.ordered s.start_regular s.finish_regular hs
    change ∀n m,coeff n (negativeCovectorUnit Ω C coord hcoord pc e (s.finish C e)*
      (negativeCovectorUnit Ω C coord hcoord pc e (s.start C e))⁻¹).val.val m≠0 → _ at hb
    have htel : (negativeCovectorUnit Ω C coord hcoord pc e (s.finish C e)*
        (negativeCovectorUnit Ω C coord hcoord pc e (s.start C e))⁻¹)*
      (negativeCovectorUnit Ω C coord hcoord pc e (s.start C e)*
        (negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹)=
      negativeCovectorUnit Ω C coord hcoord pc e (s.finish C e)*
        (negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹ := by simp only [mul_assoc,inv_mul_cancel_left]
    simpa only [←Units.val_mul,←Subring.coe_mul,htel] using
      series_support_addSubmonoid_mul LaurentRay.vUnit Ω _ _ _ hb hp

include hS hcomp in
theorem mutatedPathCompletion_rational_nocut {a b : Module.Dual ℝ E} (pos : Bool)
    (p : GenericLinePath C e a b) (hs : p.OnCutSide C pc e pos) :
    mutationSideAction LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω) pos
      (rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc) (nonpDegree coord pc) (mutationSize Ω C pc+1)
        (endpointRatioPositive Ω C coord hcoord pc e a b).val)=
    rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (mutationSize Ω C pc+1)
      (mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p) := by
  rw [(mutatedPathCompletion_nocut Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg pos p hs).2]
  exact mutation_rational_compatibility Ω hΩ C coord hcoord pc pos
    (endpointRatioPositive Ω C coord hcoord pc e a b)
    (endpointRatioPositive_nocut_cone Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg pos p hs)

include hcoord hS hcomp in
theorem mutatedPathCompletion_nocut_loop {a : Module.Dual ℝ E} (pos : Bool)
    (p : GenericLinePath C e a a) (hs : p.OnCutSide C pc e pos) :
    mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p=1 := by
  rw [(mutatedPathCompletion_nocut Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg pos p hs).2]
  simp only [mul_inv_cancel]
  exact mutationCompletion_one Ω hΩ C coord pc pos LaurentRay.vUnit
end
end ElementaryPositivity.QuantumTorus

end

end OAI
