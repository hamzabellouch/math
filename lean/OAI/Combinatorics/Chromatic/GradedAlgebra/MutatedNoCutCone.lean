import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationOrientedCompatibility

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] (v : Rˣ) (Ω : M →+ M →+ ℤ)
local instance mutatedNoCutConeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance mutatedNoCutConeAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance mutatedNoCutConeAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma series_support_addSubmonoid_one (P : AddSubmonoid M) :
    ∀n m,coeff n (1 : PowerSeries (Torus v Ω)) m≠0 → m∈P := by
  intro n m hm
  rw [coeff_one] at hm
  split_ifs at hm with hn
  · have hm0 : m=0:=by
      by_contra h
      exact hm (Finsupp.single_eq_of_ne h)
    exact hm0 ▸ P.zero_mem
  · exact False.elim (hm rfl)
lemma series_support_addSubmonoid_mul (P : AddSubmonoid M) (f g : PowerSeries (Torus v Ω))
    (hf : ∀n m,coeff n f m≠0 → m∈P) (hg : ∀n m,coeff n g m≠0 → m∈P) :
    ∀n m,coeff n (f*g) m≠0 → m∈P := by
  classical
  intro n m hm
  rw [coeff_mul,nonp_torus_eval_sum] at hm
  obtain ⟨ab,hab,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hm
  obtain ⟨a,b,ha,hb,he⟩:=torus_product_nonzero v Ω _ _ m hz
  exact he ▸ P.add_mem (hf ab.1 a ha) (hg ab.2 b hb)
end
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance mutatedNoCutConeLaurentRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance mutatedNoCutConeLaurentAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedNoCutConeLaurentAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
include hcoord hS hcomp in
lemma noncutOldLineFactor_cone (pos : Bool) (a : ℝ)
    (hs : cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    ∀n m,coeff n (noncutOldLineFactor Ω C e he L hdeg v k H a) m≠0 →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
  classical
  unfold noncutOldLineFactor
  split
  · next ha=>
    let data:=lineRayData C e he L hdeg v k H a ha
    have hf:=simple_fiber_bound Ω C coord hcoord pc e he S hS hcomp L hdeg
      data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic pos hs
    change ∀n m,coeff n (orientPowerSeries (decide (v (e data.root)<0))
      (chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val) m≠0 → _
    cases hh : decide (v (e data.root)<0)
    · exact inverse_support_addSubmonoid LaurentRay.vUnit Ω _ _ hf
    · exact hf
  · exact series_support_addSubmonoid_one LaurentRay.vUnit Ω _

include hcoord hS hcomp in
lemma noncutComparisonWord_cone (pos : Bool) (lo hi : ℝ) (N : ℕ)
    (hs : ∀a∈intervalEventList C e v k lo hi N,
      cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    ∀n m,coeff n (comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N)).val.val m≠0 →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
  let U:=fun a=>comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
    (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
    (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
    (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a)
  have HH : ∀l : List ℝ, (∀a∈l,cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) →
      ∀n m,coeff n (l.map U).prod.val.val m≠0 →
        m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
    intro l
    induction l with
    | nil=>intro _; exact series_support_addSubmonoid_one LaurentRay.vUnit Ω _
    | cons a l ih=>
      intro hl
      have ha:=hl a (by simp)
      have hb:=noncutOldLineFactor_cone Ω C coord hcoord pc e he S hS hcomp L hdeg v k H pos a ha
      rw [noncutOldLineFactor_comparison Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos a ha] at hb
      exact series_support_addSubmonoid_mul LaurentRay.vUnit Ω _ _ _ hb
        (ih (fun b hh=>hl b (List.mem_cons_of_mem a hh)))
  simpa only [comparisonWordOld,actualLineWord,List.map_map,Function.comp_def] using
    HH (intervalEventList C e v k lo hi N) hs

include hΩ he hS hcomp hdeg H in
lemma noncutEndpointRatio_cone (pos : Bool) (lo hi : ℝ) (ho : lo<hi)
    (ha : ∀N,lo∉lineEvents (realRootsThrough e C N) v k)
    (hb : ∀N,hi∉lineEvents (realRootsThrough e C N) v k)
    (hs : ∀a,lo<a → a<hi → cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    ∀n m,coeff n (lineNegativeUnit Ω C coord hcoord pc e v k hi*
        (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹).val.val m≠0 →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
  intro n m hm
  have hsN : ∀a∈intervalEventList C e v k lo hi n,
      cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc):=by
    intro a hh
    have hhF:=Finset.mem_sort (· ≥ ·) |>.mp hh
    have hab:=(Finset.mem_filter.mp hhF).2
    exact hs a hab.1 hab.2
  have hcone:=noncutComparisonWord_cone Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos lo hi n hsN
  have ht:=actualLine_old_transport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi n
    (ha n) (hb n) ho
  have HH:=oldCoefficientsEqual_mul Ω coord pc n _ _
    (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹
    (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹ ht (fun _ _=>rfl)
  simp only [mul_assoc,mul_inv_cancel,mul_one] at HH
  apply hcone n m
  rw [HH n le_rfl]
  exact hm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
