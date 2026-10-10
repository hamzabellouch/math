import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutatedHalfspaceTransport
import OAI.Combinatorics.Chromatic.QuantumTorus.MutatedCanonicalCharts
import OAI.Combinatorics.Chromatic.Walls.IncomingTransportTrace

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
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
lemma mutatedTransport_chartNegative (N : ℕ) {a b x : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) (HX : RegularCovector C e x)
    (hA : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      0<realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0)
    (hx : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) x (e m)≠0) :
    ∀n≤N, coeff n (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HX).val=
      coeff n (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e)
        (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val := by
  intro n hn
  exact (mutatedTransport_chart_three Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd N
    ((realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e)
    HA HB HX HX hA hB
    (by intro j hj m hm; exact ⟨id,fun hh=>lt_of_le_of_ne hh (Ne.symm (hx j hj m hm))⟩)
    (by intro j hj m hm; exact ⟨id,fun hh=>lt_of_le_of_ne hh (hx j hj m hm)⟩)
    n hn).2.2

include hnd in
lemma mutatedTransport_negative_ratio (N : ℕ) {a b x y : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (HX : RegularCovector C e x) (HY : RegularCovector C e y)
    (hA : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      0<realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0)
    (hx : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) x (e m)≠0)
    (hy : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) y (e m)≠0) :
    ∀n≤N, coeff n (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HX HY).val=
      coeff n ((chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) y).toAddMonoidHom.comp e)
        (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val *
        invOfUnit (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e)
        (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val 1) := by
  let T (u w : Module.Dual ℝ E) (HU : RegularCovector C e u) (HW : RegularCovector C e w):=
    mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HU HW
  have Hx:=mutatedTransport_chartNegative Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd N HA HB HX hA hB hx
  have Hy:=mutatedTransport_chartNegative Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd N HA HB HY hA hB hy
  have Hi:=FormalLog.inverse_coeff_congr _ _ (T a x HA HX).property.1
    (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc) _ (T a b HA HB)).property.1 N Hx
  have He : (T x y HX HY).val=(T a y HA HY).val*invOfUnit (T a x HA HX).val 1:=by
    have H:=mutatedTransport_trans Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HX HY
    change (T a y HA HY).val=(T x y HX HY).val*(T a x HA HX).val at H
    rw [H,mul_assoc,mul_invOfUnit _ _ (T a x HA HX).property.1,mul_one]
  intro n hn
  change coeff n (T x y HX HY).val=_
  rw [He]
  exact FormalLog.mul_coeff_congr _ _ _ _ n
    (fun j hj=>Hy j (hj.trans hn)) (fun j hj=>Hi j (hj.trans hn))
end
end ElementaryPositivity.QuantumTorus

end
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
include hnd in
lemma mutatedTransport_nocut (pos : Bool) {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (ha : cutSide pos (a.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hb : cutSide pos (b.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
      (negativeCovectorUnit Ω C coord hcoord pc e b*
        (negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹).val.val ∧
    (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val=
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (negativeCovectorUnit Ω C coord hcoord pc e b*
          (negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹).val.val := by
  obtain ⟨p,hp⟩:=generic_path_exists_onCutSide C pc e pos a b HA HB ha hb
  obtain ⟨hbound,heq⟩:=mutatedPathCompletion_nocut Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg pos p hp
  exact ⟨hbound,(mutatedTransport_eq_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HB p).trans heq⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
