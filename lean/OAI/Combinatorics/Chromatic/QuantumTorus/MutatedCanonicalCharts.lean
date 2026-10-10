import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutatedEndpoint

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
lemma mutatedTransport_chart_three (N : ℕ) (h : M →+ ℝ)
    {a b x y : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (HX : RegularCovector C e x) (HY : RegularCovector C e y)
    (hA : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      0<realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0)
    (hX : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      (h m<0 → realMutationCovector e S (simpleRoot C pc) x (e m)<0) ∧
      (0≤h m → 0<realMutationCovector e S (simpleRoot C pc) x (e m)))
    (hY : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      (0<h m → 0<realMutationCovector e S (simpleRoot C pc) y (e m)) ∧
      (h m≤0 → realMutationCovector e S (simpleRoot C pc) y (e m)<0)) :
    ∀n≤N,
      coeff n (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HY HB).val=
        coeff n (chartPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) h
          (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val ∧
      coeff n (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HX HY).val=
        coeff n (chartZero LaurentRay.vUnit Ω (mutatedRoots Ω C pc) h
          (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val ∧
      coeff n (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HX).val=
        coeff n (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc) h
          (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val := by
  let T (u w : Module.Dual ℝ E) (HU : RegularCovector C e u) (HW : RegularCovector C e w):=
    mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HU HW
  have hc:=mutatedTransport_endpoint_support Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    (fun m=>h m<0) (fun u w hu hw=>by simpa only [map_add] using add_neg hu hw) N HA HX
    (by intro n hn m hm hh; exact Or.inl ⟨hA n hn m hm,(hX n hn m hm).2 (le_of_not_gt hh)⟩)
  have ha:=mutatedTransport_endpoint_support Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    (fun m=>0<h m) (fun u w hu hw=>by simpa only [map_add] using add_pos hu hw) N HY HB
    (by intro n hn m hm hh; exact Or.inr ⟨(hY n hn m hm).2 (le_of_not_gt hh),hB n hn m hm⟩)
  have hb:=mutatedTransport_endpoint_support Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    (fun m=>h m=0) (fun u w hu hw=>by rw [map_add,hu,hw,add_zero]) N HX HY
    (by
      intro n hn m hm hh
      rcases lt_or_gt_of_ne hh with hp|hp
      · exact Or.inr ⟨(hX n hn m hm).1 hp,(hY n hn m hm).2 hp.le⟩
      · exact Or.inl ⟨(hX n hn m hm).2 hp.le,(hY n hn m hm).1 hp⟩)
  apply chart_three_truncated_unique LaurentRay.vUnit Ω (mutatedRoots Ω C pc) h
    (T a b HA HB) (T y b HY HB).val (T x y HX HY).val (T a x HA HX).val N
    (T y b HY HB).property.1 (T x y HX HY).property.1 (T a x HA HX).property.1
  · have h1:=mutatedTransport_trans Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HX HY
    have h2:=mutatedTransport_trans Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HY HB
    dsimp [T]
    rw [mul_assoc,←h1,←h2]
  · intro n hn m hm
    by_contra hh
    exact hm (ha n hn m hh)
  · intro n hn m hm
    by_contra hh
    exact hm (hb n hn m hh)
  · intro n hn m hm
    by_contra hh
    exact hm (hc n hn m hh)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
