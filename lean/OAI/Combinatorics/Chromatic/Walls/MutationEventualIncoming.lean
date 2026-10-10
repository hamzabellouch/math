import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutationIncomingFinite
import OAI.Combinatorics.Chromatic.Walls.GeometricMutationLines

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
variable (Ω : M →+ M →+ ℤ) (e : M →+ E)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : M)
variable (hS : ∀x,S x x=0) (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
lemma incoming_side_label (r : M) (pos : Bool)
    (hs : if pos then 0≤Ω p r else Ω p r≤0) :
    (if pos then r else mutationShear Ω p r)=mutationIncomingLabel Ω p r := by
  cases pos
  · exact (mutationIncomingLabel_nonpositive Ω p r hs).symm
  · exact (mutationIncomingLabel_nonnegative Ω p r hs).symm

include hcomp in
lemma incoming_line_eventual_side (r : M) (pos : Bool) (k : Module.Dual ℝ E)
    (hs : if pos then 0≤Ω p r else Ω p r≤0)
    (hz : Ω p r=0 → if pos then 0≤k (e p) else k (e p)≤0) :
    ∃T : ℝ,∀t≥T,if pos then 0≤(k+t • S.flip (e r)) (e p)
      else (k+t • S.flip (e r)) (e p)≤0 := by
  by_cases hh : Ω p r=0
  · refine ⟨0,?_⟩
    intro t ht
    simpa only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.flip_apply,
      hcomp,hh,Int.cast_zero,smul_eq_mul,mul_zero,add_zero] using hz hh
  · cases pos
    · change Ω p r≤0 at hs
      have ha : (0:ℝ)< -(Ω p r:ℝ):=by exact_mod_cast (by omega : 0< -Ω p r)
      refine ⟨(abs (k (e p))+1)/(-(Ω p r:ℝ)),?_⟩
      intro t ht
      have H:=(div_le_iff₀ ha).mp ht
      have Hk:=le_abs_self (k (e p))
      change (k+t • S.flip (e r)) (e p)≤0
      simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.flip_apply,
        hcomp,smul_eq_mul]
      nlinarith
    · change 0≤Ω p r at hs
      have ha : (0:ℝ)<(Ω p r:ℝ):=by exact_mod_cast (by omega : 0<Ω p r)
      refine ⟨(abs (k (e p))+1)/(Ω p r:ℝ),?_⟩
      intro t ht
      have H:=(div_le_iff₀ ha).mp ht
      have Hk:=neg_abs_le (k (e p))
      change 0≤(k+t • S.flip (e r)) (e p)
      simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.flip_apply,
        hcomp,smul_eq_mul]
      nlinarith

include hS hcomp in
lemma mutation_incoming_line_eventual (r : M) (pos : Bool) (k : Module.Dual ℝ E)
    (hs : if pos then 0≤Ω p r else Ω p r≤0)
    (hz : Ω p r=0 → if pos then 0≤k (e p) else k (e p)≤0) :
    ∃T : ℝ,∀t≥T,realMutationCovector e S p (k+t • S.flip (e r))=
      realSideCovector e S p pos k+t • S.flip (e (mutationIncomingLabel Ω p r)) := by
  obtain ⟨T,hT⟩:=incoming_line_eventual_side Ω e S p hcomp r pos k hs hz
  refine ⟨T,fun t ht=>?_⟩
  rw [realMutationCovector_incoming_line Ω e S p hS hcomp pos k r t (hT t ht),
    incoming_side_label Ω p r pos hs]
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {M I E : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable [AddCommGroup E] [Module ℝ E]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I) (pos : Bool)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hS hcomp hdeg in
lemma pushed_nonsimple_incoming_eventually (d dr : ℕ) (r : M) (hdr : 0<dr)
    (hr : HasRootDegree C dr r) (hn : ∀i,¬OnPositiveRay r (simpleRoot C i))
    (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C ((mutationSize Ω C pc+1)*d)) (e r) (S.flip (e r)) k)
    (hs : if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0)
    (hz : Ω (simpleRoot C pc) r=0 → if pos then 0≤k (e (simpleRoot C pc)) else k (e (simpleRoot C pc))≤0) :
    ∃T : ℝ,∀t≥T,
      realMutationCovector e S (simpleRoot C pc) (k+t • S.flip (e r))=
        realSideCovector e S (simpleRoot C pc) pos k+
          t • S.flip (e (mutationIncomingLabel Ω (simpleRoot C pc) r)) ∧
      (∀n≤d,coeff n (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (chartZero LaurentRay.vUnit Ω C ((k+t • S.flip (e r)).toAddMonoidHom.comp e)
          (simpleTotalTransport Ω C)).val)=coeff n 1) := by
  obtain ⟨A,hA⟩:=mutation_incoming_line_eventual Ω e S (simpleRoot C pc) hS hcomp r pos k hs hz
  obtain ⟨B,hB,hbound⟩:=finite_upper_bound
    (lineEvents (realRootsThrough e C ((mutationSize Ω C pc+1)*d)) (S.flip (e r)) k)
  refine ⟨max A B,fun t ht=>⟨hA t ((le_max_left A B).trans ht),?_⟩⟩
  have hb : ∀a∈lineEvents (realRootsThrough e C ((mutationSize Ω C pc+1)*d)) (S.flip (e r)) k,a<t:=by
    intro a ha
    exact lt_of_lt_of_le (hbound a ha) ((le_max_right A B).trans ht)
  have HF:=nonsimple_incoming_at_far_through Ω C e he S hS hcomp L hdeg
    ((mutationSize Ω C pc+1)*d) dr r hdr hr hn k H t hb
  intro n hnd
  rw [←mutationCompletion_one Ω hΩ C coord pc pos LaurentRay.vUnit]
  exact mutationCompletion_congr_through Ω hΩ C coord pc pos LaurentRay.vUnit _ _ n _
    (Nat.mul_le_mul_left _ hnd) HF

variable (hcoord : ∀a,coord (C a)=a)
include hcoord he hS hcomp hdeg in
lemma pushed_simple_incoming_eventually (d : ℕ) (i : I) (hi : i≠pc)
    (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C ((mutationSize Ω C pc+1)*d))
      (e (simpleRoot C i)) (S.flip (e (simpleRoot C i))) k)
    (hs : if pos then 0 ≤ mutationPairing Ω C pc i else mutationPairing Ω C pc i≤0)
    (hz : mutationPairing Ω C pc i=0 →
      if pos then 0≤k (e (simpleRoot C pc)) else k (e (simpleRoot C pc))≤0) :
    ∃T : ℝ,∀t≥T,
      realMutationCovector e S (simpleRoot C pc) (k+t • S.flip (e (simpleRoot C i)))=
        realSideCovector e S (simpleRoot C pc) pos k+
          t • S.flip (e (simpleRoot (mutatedRoots Ω C pc) i)) ∧
      (∀n≤d,coeff n (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (chartZero LaurentRay.vUnit Ω C
          ((k+t • S.flip (e (simpleRoot C i))).toAddMonoidHom.comp e)
          (simpleTotalTransport Ω C)).val)=
        coeff n (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) i))) := by
  obtain ⟨A,hA⟩:=mutation_incoming_line_eventual Ω e S (simpleRoot C pc) hS hcomp
    (simpleRoot C i) pos k hs hz
  obtain ⟨B,hB,hbound⟩:=finite_upper_bound
    (lineEvents (realRootsThrough e C ((mutationSize Ω C pc+1)*d)) (S.flip (e (simpleRoot C i))) k)
  refine ⟨max A B,fun t ht=>⟨?_,?_⟩⟩
  · rw [hA t ((le_max_left A B).trans ht),mutationIncomingLabel_simple Ω C pc i hi]
  · have htne : t∉lineEvents (realRootsThrough e C ((mutationSize Ω C pc+1)*d))
        (S.flip (e (simpleRoot C i))) k:=by
      intro htmem
      exact (lt_irrefl t) (lt_of_lt_of_le (hbound t htmem) ((le_max_right A B).trans ht))
    have hg:=line_generic e he C L hdeg ((mutationSize Ω C pc+1)*d) 1 (simpleRoot C i)
      (by omega) (simpleRoot_degree C i) (S.flip (e (simpleRoot C i))) k
      (hS (e (simpleRoot C i))) H t htne
    intro n hnd
    exact actual_simple_wall_mutation_through Ω hΩ C coord hcoord pc pos i hi hs _ n
      (hg.mono C (Nat.mul_le_mul_left _ hnd))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
