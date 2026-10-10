import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutatedPathIndependent
import OAI.Combinatorics.Chromatic.QuantumTorus.MutationConvexSigns

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : M) (hS : ∀x,S x x=0)

def mutationSignRegion (P : Finset E) : Set (Module.Dual ℝ E) :=
  {h | ∀x∈P,0<realMutationCovector e S p h x}

include hS in
omit [FiniteDimensional ℝ E] in
lemma cut_positive_intermediate (P : Finset E) (a b : Module.Dual ℝ E)
    (ha : a∈mutationSignRegion e S p P) (hb : b∈mutationSignRegion e S p P)
    (hap : a (e p)<0) (hbp : 0<b (e p)) :
    ∃k : Module.Dual ℝ E,k (e p)=0 ∧
      ∀x∈P,0<k x ∧ 0<k (realShearVector e S p x) := by
  let t:=-a (e p)/(b (e p)-a (e p))
  have hden : 0<b (e p)-a (e p):=by linarith
  have ht : 0<t:=div_pos (neg_pos.mpr hap) hden
  have ht1 : t<1:=by change -a (e p)/(b (e p)-a (e p))<1; rw [div_lt_one hden]; linarith
  let k:=(1-t) • realMutationCovector e S p a+t • realMutationCovector e S p b
  have hk : k (e p)=0:=by
    simp only [k,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
      realMutationCovector_at_p e S p hS]
    dsimp [t]
    field_simp
    ring
  refine ⟨k,hk,?_⟩
  intro x hx
  have hkp : 0<k x:=by
    change 0<(1-t)*realMutationCovector e S p a x+t*realMutationCovector e S p b x
    exact real_convex_pos _ _ _ (ha x hx) (hb x hx) ht.le ht1.le
  refine ⟨hkp,?_⟩
  simpa only [realShearVector,map_add,map_smul,hk,smul_zero,add_zero] using hkp

include hS in
lemma generic_mutation_region_path (P : Finset E) (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (ha : a∈mutationSignRegion e S p P) (hb : b∈mutationSignRegion e S p P)
    (hap : a (e p)≠0) (hbp : b (e p)≠0) :
    ∃q : GenericLinePath C e a b,q.InRegion C e (mutationSignRegion e S p P) := by
  classical
  have hpositive (g : Module.Dual ℝ E) (hg : 0<g (e p)) :
      realMutationCovector e S p g=g:=ite_eq_left hg.le
  have hnegative (g : Module.Dual ℝ E) (hg : g (e p)<0) :
      realMutationCovector e S p g=realShearCovector e S p g:=ite_eq_right (not_le.mpr hg)
  by_cases hpa : 0<a (e p)
  · by_cases hpb : 0<b (e p)
    · apply generic_region_path_via C e a b a (insert (e p) P) HA HB
      intro h Hh
      have hhp : 0<h (e p):=(Hh _ (Finset.mem_insert_self _ _)).1 hpa
      have hhr : h∈mutationSignRegion e S p P:=by
        intro x hx
        rw [hpositive h hhp]
        apply (Hh x (Finset.mem_insert_of_mem hx)).1
        simpa only [hpositive a hpa] using ha x hx
      constructor
      · intro t ht ht1 x hx
        exact mutation_segment_same_side e S p a h x (ha x hx) (hhr x hx)
          (Or.inl ⟨hpa.le,hhp.le⟩) t ht ht1
      · intro t ht ht1 x hx
        exact mutation_segment_same_side e S p h b x (hhr x hx) (hb x hx)
          (Or.inl ⟨hhp.le,hpb.le⟩) t ht ht1
    · have hpb' : b (e p)<0:=lt_of_le_of_ne (le_of_not_gt hpb) hbp
      obtain ⟨k,_,Hk⟩:=cut_positive_intermediate e S p hS P b a hb ha hpb' hpa
      apply generic_region_path_via C e a b k (P∪P.image (realShearVector e S p)) HA HB
      intro h Hh
      have hh (x : E) (hx : x∈P) : 0<h x ∧ 0<h (realShearVector e S p x):=
        ⟨(Hh x (Finset.mem_union_left _ hx)).1 (Hk x hx).1,
          (Hh _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))).1 (Hk x hx).2⟩
      constructor
      · intro t ht ht1 x hx
        exact mutation_segment_with_both e S p a h x (ha x hx) (hh x hx) t ht ht1
      · intro t ht ht1 x hx
        have H:=mutation_segment_with_both e S p b h x (hb x hx) (hh x hx) (1-t)
          (sub_nonneg.mpr ht1) (by linarith)
        have heq : (1-(1-t)) • b+(1-t) • h=(1-t) • h+t • b:=by module
        rwa [heq] at H
  · have hpa' : a (e p)<0:=lt_of_le_of_ne (le_of_not_gt hpa) hap
    by_cases hpb : 0<b (e p)
    · obtain ⟨k,_,Hk⟩:=cut_positive_intermediate e S p hS P a b ha hb hpa' hpb
      apply generic_region_path_via C e a b k (P∪P.image (realShearVector e S p)) HA HB
      intro h Hh
      have hh (x : E) (hx : x∈P) : 0<h x ∧ 0<h (realShearVector e S p x):=
        ⟨(Hh x (Finset.mem_union_left _ hx)).1 (Hk x hx).1,
          (Hh _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))).1 (Hk x hx).2⟩
      constructor
      · intro t ht ht1 x hx
        exact mutation_segment_with_both e S p a h x (ha x hx) (hh x hx) t ht ht1
      · intro t ht ht1 x hx
        have H:=mutation_segment_with_both e S p b h x (hb x hx) (hh x hx) (1-t)
          (sub_nonneg.mpr ht1) (by linarith)
        have heq : (1-(1-t)) • b+(1-t) • h=(1-t) • h+t • b:=by module
        rwa [heq] at H
    · have hpb' : b (e p)<0:=lt_of_le_of_ne (le_of_not_gt hpb) hbp
      apply generic_region_path_via C e a b a (insert (e p) (P.image (realShearVector e S p))) HA HB
      intro h Hh
      have hhp : h (e p)<0:=(Hh _ (Finset.mem_insert_self _ _)).2 hpa'
      have hhr : h∈mutationSignRegion e S p P:=by
        intro x hx
        rw [hnegative h hhp,realShearCovector_eval]
        apply (Hh _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x,hx,rfl⟩))).1
        simpa only [hnegative a hpa',realShearCovector_eval] using ha x hx
      constructor
      · intro t ht ht1 x hx
        exact mutation_segment_same_side e S p a h x (ha x hx) (hhr x hx)
          (Or.inr ⟨hpa'.le,hhp.le⟩) t ht ht1
      · intro t ht ht1 x hx
        exact mutation_segment_same_side e S p h b x (hhr x hx) (hb x hx)
          (Or.inr ⟨hhp.le,hpb'.le⟩) t ht ht1
end
end ElementaryPositivity.QuantumTorus

end
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
local instance mutationChamberPathsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance mutationChamberPathsAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutationChamberPathsAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

include hcoord hS hcomp in
omit [FiniteDimensional ℝ E] in
lemma mutatedLineFactor_protected (P : Finset E) (V : M → Prop) (D : ℕ)
    (hP : ∀n,n+1≤D → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      ¬V m → e m∈P ∨ -(e m)∈P)
    (v k : Module.Dual ℝ E) (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : k+a • v∈mutationSignRegion e S (simpleRoot C pc) P) :
    ∀n,n+1≤D → SupportedOn LaurentRay.vUnit Ω V
      (coeff (n+1) (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a)) := by
  intro n hn m hm
  by_contra hh
  have hd : HasRootDegree (mutatedRoots Ω C pc) (n+1) m:=by
    by_contra hr
    exact hh (mutatedLineFactor_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a
      (n+1) m hr)
  have hk:=mutatedLineFactor_kernel Ω hΩ C coord pc e he S hS hcomp L hdeg v k H a (n+1) m hh
  rcases hP n hn m hd hm with hp|hp
  · have Hpos:=ha (e m) hp
    linarith
  · have Hpos:=ha (-e m) hp
    rw [map_neg,hk,neg_zero] at Hpos
    exact (lt_irrefl 0) Hpos

include hcoord hS hcomp in
omit [FiniteDimensional ℝ E] in
lemma mutatedLineProduct_protected (P : Finset E) (V : M → Prop)
    (hV : ∀a b,V a → V b → V (a+b)) (D : ℕ)
    (hP : ∀n,n+1≤D → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      ¬V m → e m∈P ∨ -(e m)∈P)
    (v k : Module.Dual ℝ E) (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
    (lo hi : ℝ) (N : ℕ)
    (hregion : ∀a,lo≤a → a≤hi → k+a • v∈mutationSignRegion e S (simpleRoot C pc) P) :
    ∀n,n+1≤D → SupportedOn LaurentRay.vUnit Ω V
      (coeff (n+1) (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N)) := by
  let F (a : ℝ) : CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc):=
    ⟨mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a,
      mutatedLineFactor_constant Ω hΩ C coord pc e he L hdeg v k H a,
      mutatedLineFactor_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a⟩
  apply strict_list_product_through LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
    (intervalEventList C e v k lo hi N) F V hV D
  intro a ha
  have haF : a∈intervalLineEvents C e v k lo hi N:=Finset.mem_sort _ |>.mp ha
  have hab:=(Finset.mem_filter.mp haF).2
  exact mutatedLineFactor_protected Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
    P V D hP v k H a (hregion a hab.1.le hab.2.le)

include hcoord hS hcomp in
omit [FiniteDimensional ℝ E] in
lemma mutatedPathCompletion_protected (P : Finset E) (V : M → Prop)
    (hV : ∀a b,V a → V b → V (a+b)) (D : ℕ)
    (hP : ∀n,n+1≤D → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      ¬V m → e m∈P ∨ -(e m)∈P)
    {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b)
    (hp : p.InRegion C e (mutationSignRegion e S (simpleRoot C pc) P)) :
    ∀n,n+1≤D → SupportedOn LaurentRay.vUnit Ω V
      (coeff (n+1) (mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p)) := by
  induction p with
  | nil=>
    intro n hn
    simp only [mutatedPathCompletion,coeff_one,show n+1≠0 by omega,ite_false]
    exact SupportedOn.zero LaurentRay.vUnit Ω V
  | append s p ih=>
    apply strict_mul_through LaurentRay.vUnit Ω V hV _ _ D
      (mutatedLineCompletion_constant Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic s.lo s.hi)
      (mutatedPathCompletion_constant Ω hΩ C coord pc e he L hdeg p) _ (ih hp.2)
    intro n hn
    rw [mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic s.lo s.hi
      (n+1) (max 1 ((mutationSize Ω C pc+1)*D)) (le_max_left _ _)
      ((Nat.mul_le_mul_left _ hn).trans (le_max_right _ _))]
    exact mutatedLineProduct_protected Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      P V hV D hP s.direction s.offset s.generic s.lo s.hi _ hp.1 n hn
end

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
lemma mutatedTransport_protected (P : Finset E) (V : M → Prop)
    (hV : ∀a b,V a → V b → V (a+b)) (D : ℕ)
    (hP : ∀n,n+1≤D → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      ¬V m → e m∈P ∨ -(e m)∈P)
    {a b : Module.Dual ℝ E} (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (ha : a∈mutationSignRegion e S (simpleRoot C pc) P)
    (hb : b∈mutationSignRegion e S (simpleRoot C pc) P)
    (hap : a (e (simpleRoot C pc))≠0) (hbp : b (e (simpleRoot C pc))≠0) :
    ∀n,n+1≤D → SupportedOn LaurentRay.vUnit Ω V
      (coeff (n+1) (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val) := by
  obtain ⟨q,hq⟩:=generic_mutation_region_path C e S (simpleRoot C pc) hS P a b HA HB ha hb hap hbp
  rw [mutatedTransport_eq_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HB q]
  exact mutatedPathCompletion_protected Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg P V hV D hP q hq
end
end ElementaryPositivity.QuantumTorus

end

end OAI
