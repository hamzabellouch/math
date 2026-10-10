import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PathOldTransport
import OAI.Combinatorics.Chromatic.Walls.GenericLineJoining

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
lemma comparisonWordAction_append {K M : Type*} [Field K] [AddCommGroup M]
    (u : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
    (δ k : M →+ ℤ) (p : M) (hp : k p=1) (B : ℕ)
    (l l' : List (ComparisonCrossing u Ω δ k B))
    (f : PowerSeries (FiberTorus u (complementOmega k Ω) (complementAlpha k p Ω))) :
    comparisonWordAction u Ω hΩ δ k p hp B (l++l') f=
    comparisonWordAction u Ω hΩ δ k p hp B l (comparisonWordAction u Ω hΩ δ k p hp B l' f) := by
  simp only [comparisonWordAction,List.foldr_append]

lemma comparisonWordAction_input_congr {K M : Type*} [Field K] [AddCommGroup M]
    (u : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
    (δ k : M →+ ℤ) (p : M) (hp : k p=1) (B : ℕ)
    (l : List (ComparisonCrossing u Ω δ k B))
    (f g : PowerSeries (FiberTorus u (complementOmega k Ω) (complementAlpha k p Ω)))
    (N : ℕ) (hg : ∀n≤N,coeff n f=coeff n g) :
    ∀n≤N,coeff n (comparisonWordAction u Ω hΩ δ k p hp B l f)=
      coeff n (comparisonWordAction u Ω hΩ δ k p hp B l g) := by
  induction l with
  | nil=>exact hg
  | cons c l ih=>
    intro n hn
    exact comparisonAction_input_congr u Ω hΩ δ k p hp B c _ _ n
      (fun j hj=>ih j (hj.trans hn))

variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

lemma actualPathWord_trans {a b c : Module.Dual ℝ E}
    (p : GenericLinePath C e a b) (q : GenericLinePath C e b c) (N : ℕ) :
    actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg (p.trans C e q) N=
      actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg q N++
      actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N := by
  induction q with
  | nil=>rfl
  | append s q ih=>
    simp only [GenericLinePath.trans,actualPathWord,ih,List.append_assoc]

def actualPathAction {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :=
  PowerSeries.mk (fun D=>coeff D
    (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p
        (max 1 ((mutationSize Ω C pc+1)*D))) f))

lemma actualPathAction_coeff {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)))
    (D A : ℕ) (hA : 1≤A) (hDA : (mutationSize Ω C pc+1)*D≤A) :
    coeff D (actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p f)=
    coeff D (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p A) f) := by
  simp only [actualPathAction,PowerSeries.coeff_mk]
  exact (actualPathWord_refines Ω C coord hcoord pc e he S hS hcomp L hdeg p D
    (max 1 ((mutationSize Ω C pc+1)*D)) A (le_max_left _ _) (le_max_right _ _)
    (max_le hA hDA)).action _ _ _ _ _ _ _ _ f f (fun _ _=>rfl) D le_rfl

include he hdeg in
theorem actualPathAction_loop {a : Module.Dual ℝ E} (p : GenericLinePath C e a a)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p f=f := by
  apply PowerSeries.ext
  intro D
  simp only [actualPathAction,PowerSeries.coeff_mk]
  exact actualPath_rational_loop_coefficient Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p D f

theorem actualPathAction_trans {a b c : Module.Dual ℝ E}
    (p : GenericLinePath C e a b) (q : GenericLinePath C e b c)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg (p.trans C e q) f=
      actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg q
        (actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p f) := by
  apply PowerSeries.ext
  intro D
  let A:=max 1 ((mutationSize Ω C pc+1)*D)
  rw [actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg _ _ D A
      (le_max_left _ _) (le_max_right _ _),actualPathWord_trans,comparisonWordAction_append]
  rw [actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg q _ D A
    (le_max_left _ _) (le_max_right _ _)]
  apply comparisonWordAction_input_congr _ _ _ _ _ _ _ _ _ _ _ D _ D le_rfl
  intro n hn
  exact (actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p f n A
    (le_max_left _ _) ((Nat.mul_le_mul_left _ hn).trans (le_max_right _ _))).symm
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
def GenericLineSegment.avoidsCut (s : GenericLineSegment C e) (z : E) : Prop :=
  ∀t,s.lo ≤ t → t ≤ s.hi → (s.offset+t • s.direction) z≠0

def GenericLinePath.avoidsCut {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) (z : E) : Prop :=
  match p with
  | .nil _=>True
  | .append s p=>s.avoidsCut C e z ∧ p.avoidsCut z

def GenericLinePath.castEnds {a b a' b' : Module.Dual ℝ E}
    (h0 : a=a') (h1 : b=b') (p : GenericLinePath C e a b) : GenericLinePath C e a' b' :=
  h0 ▸ h1 ▸ p
lemma GenericLinePath.avoidsCut_castEnds {a b a' b' : Module.Dual ℝ E}
    (h0 : a=a') (h1 : b=b') (p : GenericLinePath C e a b) (z : E) :
    (p.castEnds C e h0 h1).avoidsCut C e z ↔ p.avoidsCut C e z := by
  subst a'; subst b'; rfl

lemma GenericLinePath.avoidsCut_trans {a b c : Module.Dual ℝ E}
    (p : GenericLinePath C e a b) (q : GenericLinePath C e b c) (z : E)
    (hp : p.avoidsCut C e z) (hq : q.avoidsCut C e z) :
    (p.trans C e q).avoidsCut C e z := by
  induction q with
  | nil=>exact hp
  | append s q ih=>exact ⟨hq.1,ih hq.2⟩

lemma segment_avoidsCut_of_sign (s : GenericLineSegment C e) (z : E)
    (H : (0<s.start C e z ∧ 0<s.finish C e z) ∨
      (s.start C e z<0 ∧ s.finish C e z<0)) : s.avoidsCut C e z := by
  intro t hlo hhi hz
  simp only [GenericLineSegment.start,GenericLineSegment.finish,
    LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] at H hz
  by_cases hv : 0 ≤ s.direction z
  · rcases H with H|H
    · have hd : 0≤(t-s.lo)*s.direction z:=mul_nonneg (sub_nonneg.mpr hlo) hv
      nlinarith [H.1]
    · have hd : 0≤(s.hi-t)*s.direction z:=mul_nonneg (sub_nonneg.mpr hhi) hv
      nlinarith [H.2]
  · have hv' : s.direction z≤0:=le_of_lt (lt_of_not_ge hv)
    rcases H with H|H
    · have hd : (s.hi-t)*s.direction z≤0:=mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hhi) hv'
      nlinarith [H.2]
    · have hd : (t-s.lo)*s.direction z≤0:=mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlo) hv'
      nlinarith [H.1]
end

noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
theorem generic_path_avoiding_cut_exists (a b : Module.Dual ℝ E) (z : E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (Hside : (0<a z ∧ 0<b z) ∨ (a z<0 ∧ b z<0)) :
    ∃p : GenericLinePath C e a b,p.avoidsCut C e z := by
  classical
  obtain ⟨h,Ha,Hb,HP⟩:=generic_for_two_directions (realRootsThrough e C) a b a {z}
  have HH : RegularCovector C e h:=by
    intro N s hs hn
    exact (Ha N).avoid s hs (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  have Hsign:=HP z (Finset.mem_singleton_self z)
  let s:=segmentBetween C e a h HA HH (fun N=>(Ha N).join (HA N))
  let t:=segmentBetween C e h b HH HB (fun N=>(Hb N).join_reverse (HB N))
  have hs : s.avoidsCut C e z:=by
    apply segment_avoidsCut_of_sign C e
    simp only [s,segmentBetween_start,segmentBetween_finish]
    rcases Hside with H|H
    · exact Or.inl ⟨H.1,Hsign.1 H.1⟩
    · exact Or.inr ⟨H.1,Hsign.2 H.1⟩
  have ht : t.avoidsCut C e z:=by
    apply segment_avoidsCut_of_sign C e
    simp only [t,segmentBetween_start,segmentBetween_finish]
    rcases Hside with H|H
    · exact Or.inl ⟨Hsign.1 H.1,H.2⟩
    · exact Or.inr ⟨Hsign.2 H.1,H.2⟩
  let p:=(GenericLinePath.single C e s).castEnds C e
    (segmentBetween_start C e a h HA HH _) (segmentBetween_finish C e a h HA HH _)
  let q:=(GenericLinePath.single C e t).castEnds C e
    (segmentBetween_start C e h b HH HB _) (segmentBetween_finish C e h b HH HB _)
  have hp : p.avoidsCut C e z:=by
    apply (GenericLinePath.avoidsCut_castEnds C e _ _ _ z).mpr
    exact ⟨hs,True.intro⟩
  have hq : q.avoidsCut C e z:=by
    apply (GenericLinePath.avoidsCut_castEnds C e _ _ _ z).mpr
    exact ⟨ht,True.intro⟩
  exact ⟨p.trans C e q,p.avoidsCut_trans C e q z hp hq⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
