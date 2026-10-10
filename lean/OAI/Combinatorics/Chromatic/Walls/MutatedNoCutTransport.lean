import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutatedPathCompletion

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance mutatedNoCutTransportRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance mutatedNoCutTransportAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedNoCutTransportAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

lemma mutatedLineProduct_nocut_eq (pos : Bool) (lo hi : ℝ) (N : ℕ)
    (hs : ∀a∈intervalEventList C e v k lo hi N,
      cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N=
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
          (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
          (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
          (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N)).val.val := by
  classical
  let U:=fun a=>comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
    (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
    (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
    (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a)
  have HH : ∀l : List ℝ, (∀a∈l,cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) →
      RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
        (l.map U).prod.val.val ∧
      (l.map (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H)).prod=
        mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (l.map U).prod.val.val := by
    intro l
    induction l with
    | nil=>
      intro _
      exact ⟨RegradeBound.one _ _ _ _,(mutationCompletion_one Ω hΩ C coord pc pos LaurentRay.vUnit).symm⟩
    | cons a l ih=>
      intro hl
      obtain ⟨ht,ih⟩:=ih (fun b hb=>hl b (List.mem_cons_of_mem a hb))
      have ha:=hl a (by simp)
      have heq : noncutOldLineFactor Ω C e he L hdeg v k H a=(U a).val.val:=
        noncutOldLineFactor_comparison Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos a ha
      have hb : RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos)
          (mutationSize Ω C pc+1) (U a).val.val:=by
        rw [←heq]
        exact noncutOldLineFactor_bound Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos a ha
      have hf:=mutatedLineFactor_nocut Ω hΩ C coord pc e he L hdeg v k H pos a ha
      rw [heq] at hf
      change RegradeBound _ _ _ _ ((U a).val.val*(l.map U).prod.val.val) ∧
        mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a*
          (l.map (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H)).prod=_
      refine ⟨hb.mul _ _ _ _ ht,?_⟩
      rw [hf,ih,←mutationCompletion_mul Ω hΩ C coord pc pos LaurentRay.vUnit hb ht]
      rfl
  simpa only [mutatedLineProduct,comparisonWordOld,actualLineWord,List.map_map,Function.comp_def]
    using (HH (intervalEventList C e v k lo hi N) hs).2

include hS hcomp in
lemma mutatedLineCompletion_nocut (pos : Bool) (lo hi : ℝ) (horder : lo<hi)
    (hlo : ∀N,lo∉lineEvents (realRootsThrough e C N) v k)
    (hhi : ∀N,hi∉lineEvents (realRootsThrough e C N) v k)
    (hs : ∀a,lo<a → a<hi → cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    mutatedLineCompletion Ω hΩ C coord pc e he L hdeg v k H lo hi=
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (lineNegativeUnit Ω C coord hcoord pc e v k hi*
          (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹).val.val := by
  classical
  apply PowerSeries.ext
  intro d
  let N:=max 1 ((mutationSize Ω C pc+1)*d)
  have hN : 1≤N:=le_max_left _ _
  have hdN : (mutationSize Ω C pc+1)*d≤N:=le_max_right _ _
  rw [mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg v k H lo hi d N hN hdN]
  have hsN : ∀a∈intervalEventList C e v k lo hi N,
      cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc):=by
    intro a ha
    have haF:=Finset.mem_sort (· ≥ ·) |>.mp ha
    have hab:=(Finset.mem_filter.mp haF).2
    exact hs a hab.1 hab.2
  rw [mutatedLineProduct_nocut_eq Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos lo hi N hsN]
  apply mutationCompletion_congr_through Ω hΩ C coord pc pos LaurentRay.vUnit _ _ d N hdN
  have ht:=actualLine_old_transport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N
    (hlo N) (hhi N) horder
  have HH:=oldCoefficientsEqual_mul Ω coord pc N _ _
    (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹
    (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹ ht (fun _ _=>rfl)
  simpa only [mul_assoc,mul_inv_cancel,mul_one,oldCoefficientsEqual] using HH
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
local instance mutatedNoCutTransportPathRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance mutatedNoCutTransportPathAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedNoCutTransportPathAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

lemma noncutComparisonWord_bound (pos : Bool) (lo hi : ℝ) (N : ℕ)
    (hs : ∀a∈intervalEventList C e v k lo hi N,
      cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
      (comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N)).val.val := by
  let U:=fun a=>comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
    (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
    (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
    (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a)
  have HH : ∀l : List ℝ, (∀a∈l,cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) →
      RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
        (l.map U).prod.val.val := by
    intro l
    induction l with
    | nil=>intro _; exact RegradeBound.one _ _ _ _
    | cons a l ih=>
      intro hl
      have ha:=hl a (by simp)
      have hb:=noncutOldLineFactor_bound Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos a ha
      rw [noncutOldLineFactor_comparison Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos a ha] at hb
      exact hb.mul _ _ _ _ (ih (fun b hh=>hl b (List.mem_cons_of_mem a hh)))
  simpa only [comparisonWordOld,actualLineWord,List.map_map,Function.comp_def] using
    HH (intervalEventList C e v k lo hi N) hs

include hΩ he hS hcomp hdeg H in
lemma noncutEndpointRatio_bound (pos : Bool) (lo hi : ℝ) (ho : lo<hi)
    (ha : ∀N,lo∉lineEvents (realRootsThrough e C N) v k)
    (hb : ∀N,hi∉lineEvents (realRootsThrough e C N) v k)
    (hs : ∀a,lo<a → a<hi → cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
      (lineNegativeUnit Ω C coord hcoord pc e v k hi*
        (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹).val.val := by
  intro n m hm
  have hsN : ∀a∈intervalEventList C e v k lo hi n,
      cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc):=by
    intro a hh
    have hhF:=Finset.mem_sort (· ≥ ·) |>.mp hh
    have hab:=(Finset.mem_filter.mp hhF).2
    exact hs a hab.1 hab.2
  have hbnd:=noncutComparisonWord_bound Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos lo hi n hsN
  have ht:=actualLine_old_transport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi n
    (ha n) (hb n) ho
  have HH:=oldCoefficientsEqual_mul Ω coord pc n _ _
    (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹
    (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹ ht (fun _ _=>rfl)
  simp only [mul_assoc,mul_inv_cancel,mul_one] at HH
  apply hbnd n m
  rw [HH n le_rfl]
  exact hm

def negativeCovectorUnit (a : Module.Dual ℝ E) := completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
  (chartNegative LaurentRay.vUnit Ω C (a.toAddMonoidHom.comp e) (simpleTotalTransport Ω C))

def GenericLinePath.OnCutSide (pos : Bool) {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) : Prop :=
  match p with
  | .nil _=>True
  | .append s p=>(∀t,s.lo<t → t<s.hi →
      cutSide pos ((s.offset+t • s.direction).toAddMonoidHom.comp e) (simpleRoot C pc)) ∧
      GenericLinePath.OnCutSide pos p

include hS hcomp in
lemma mutatedPathCompletion_nocut {a b : Module.Dual ℝ E} (pos : Bool) (p : GenericLinePath C e a b)
    (hs : p.OnCutSide C pc e pos) :
    RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
      (negativeCovectorUnit Ω C coord hcoord pc e b*(negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹).val.val ∧
    mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p=
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (negativeCovectorUnit Ω C coord hcoord pc e b*(negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹).val.val := by
  induction p with
  | nil=>
    simp only [mul_inv_cancel]
    exact ⟨RegradeBound.one _ _ _ _,(mutationCompletion_one Ω hΩ C coord pc pos LaurentRay.vUnit).symm⟩
  | append s p ih=>
    obtain ⟨hs,ht⟩:=hs
    obtain ⟨hp,ih⟩:=ih ht
    have hb:=noncutEndpointRatio_bound Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic pos s.lo s.hi s.ordered s.start_regular s.finish_regular hs
    have heq:=mutatedLineCompletion_nocut Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic pos s.lo s.hi s.ordered s.start_regular s.finish_regular hs
    change RegradeBound _ _ _ _
      (negativeCovectorUnit Ω C coord hcoord pc e (s.finish C e)*
        (negativeCovectorUnit Ω C coord hcoord pc e (s.start C e))⁻¹).val.val at hb
    change mutatedLineCompletion Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic s.lo s.hi=
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (negativeCovectorUnit Ω C coord hcoord pc e (s.finish C e)*
          (negativeCovectorUnit Ω C coord hcoord pc e (s.start C e))⁻¹).val.val at heq
    have htel : (negativeCovectorUnit Ω C coord hcoord pc e (s.finish C e)*
        (negativeCovectorUnit Ω C coord hcoord pc e (s.start C e))⁻¹)*
      (negativeCovectorUnit Ω C coord hcoord pc e (s.start C e)*
        (negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹)=
      negativeCovectorUnit Ω C coord hcoord pc e (s.finish C e)*
        (negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹ := by simp only [mul_assoc,inv_mul_cancel_left]
    refine ⟨?_,?_⟩
    · simpa only [←Units.val_mul,←Subring.coe_mul,htel] using hb.mul _ _ _ _ hp
    · change mutatedLineCompletion Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic s.lo s.hi*
        mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p=_
      rw [heq,ih,←mutationCompletion_mul Ω hΩ C coord pc pos LaurentRay.vUnit hb hp]
      exact congrArg (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit)
        (congrArg (fun u=>u.val.val) htel)

include hcoord hS hcomp in
theorem mutatedPathCompletion_nocut_independent {a b : Module.Dual ℝ E} (pos : Bool)
    (p q : GenericLinePath C e a b) (hp : p.OnCutSide C pc e pos) (hq : q.OnCutSide C pc e pos) :
    mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p=
      mutatedPathCompletion Ω hΩ C coord pc e he L hdeg q :=
  (mutatedPathCompletion_nocut Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg pos p hp).2.trans
    (mutatedPathCompletion_nocut Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg pos q hq).2.symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
