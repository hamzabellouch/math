import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CompletedPathAction

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (B : ℕ)
def ComparisonCrossing.IsBounded : ComparisonCrossing v Ω δ k B → Prop
  | .bounded _ _ _=>True
  | .pure _=>False
lemma boundedAction_preserves_laurent (c : ComparisonCrossing v Ω δ k B)
    (hc : c.IsBounded v Ω δ k B) (f : PowerSeries (Torus v Ω)) :
    ∃g : PowerSeries (Torus v Ω),comparisonAction v Ω hΩ δ k p hp B c
      (PowerSeries.map (embed v Ω hΩ k p hp) f)=PowerSeries.map (embed v Ω hΩ k p hp) g := by
  cases c with
  | pure b=>exact hc.elim
  | bounded u hf hi=>
    refine ⟨regrade v Ω δ B u.val.val*f*regrade v Ω δ B u.inv.val,?_⟩
    change rationalRegrade v Ω hΩ k p hp δ B u.val.val*
      PowerSeries.map (embed v Ω hΩ k p hp) f*
      rationalRegrade v Ω hΩ k p hp δ B u.inv.val=_
    simp only [rationalRegrade,map_mul]
lemma boundedWord_preserves_laurent (l : List (ComparisonCrossing v Ω δ k B))
    (hl : ∀c∈l,c.IsBounded v Ω δ k B) (f : PowerSeries (Torus v Ω)) :
    ∃g : PowerSeries (Torus v Ω),comparisonWordAction v Ω hΩ δ k p hp B l
      (PowerSeries.map (embed v Ω hΩ k p hp) f)=PowerSeries.map (embed v Ω hΩ k p hp) g := by
  induction l with
  | nil=>exact ⟨f,rfl⟩
  | cons c l ih=>
    obtain ⟨g,hg⟩:=ih (fun d hd=>hl d (List.mem_cons_of_mem c hd))
    obtain ⟨g',hg'⟩:=boundedAction_preserves_laurent v Ω hΩ δ k p hp B c
      (hl c (List.mem_cons_self)) g
    refine ⟨g',?_⟩
    change comparisonAction v Ω hΩ δ k p hp B c
      (comparisonWordAction v Ω hΩ δ k p hp B l (PowerSeries.map (embed v Ω hΩ k p hp) f))=_
    rw [hg]
    exact hg'
end
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
lemma actualLineLetter_bounded (v k : Module.Dual ℝ E)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k) (a : ℝ)
    (hp : (k+a • v) (e (simpleRoot C pc))≠0) :
    (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a).IsBounded
      LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc) (mutationSize Ω C pc+1) := by
  classical
  unfold actualLineLetter
  simp only [dite_eq_right hp]
  split_ifs with ha
  · unfold orientedBounded
    split_ifs <;> trivial
  · trivial

lemma actualLineWord_bounded (s : GenericLineSegment C e)
    (hs : s.avoidsCut C e (e (simpleRoot C pc))) (N : ℕ) :
    ∀c∈actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi N,
      c.IsBounded LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc) (mutationSize Ω C pc+1) := by
  intro c hc
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hc
  have ha' : a∈intervalLineEvents C e s.direction s.offset s.lo s.hi N:=
    (Finset.mem_sort _).mp ha
  have hi:=(Finset.mem_filter.mp ha').2
  exact actualLineLetter_bounded Ω C coord hcoord pc e he S hS hcomp L hdeg
    s.direction s.offset s.generic a (hs a (le_of_lt hi.1) (le_of_lt hi.2))

lemma actualPathWord_bounded {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b)
    (hp : p.avoidsCut C e (e (simpleRoot C pc))) (N : ℕ) :
    ∀c∈actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N,
      c.IsBounded LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc) (mutationSize Ω C pc+1) := by
  induction p with
  | nil=>simp only [actualPathWord,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | append s p ih=>
    intro c hc
    rcases List.mem_append.mp hc with hc|hc
    · exact actualLineWord_bounded Ω C coord hcoord pc e he S hS hcomp L hdeg s hp.1 N c hc
    · exact ih hp.2 c hc

theorem actualPathAction_finite_laurent {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b)
    (hp : p.avoidsCut C e (e (simpleRoot C pc)))
    (f : PowerSeries (Torus LaurentRay.vUnit Ω)) (D : ℕ) :
    ∃g : Torus LaurentRay.vUnit Ω,
      coeff D (actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p
        (PowerSeries.map (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
          (pureDegree_simple_self C coord hcoord pc)) f))=
      embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc) g := by
  let A:=max 1 ((mutationSize Ω C pc+1)*D)
  obtain ⟨g,hg⟩:=boundedWord_preserves_laurent LaurentRay.vUnit Ω hΩ
    (nonpDegree coord pc) (pureDegree coord pc) (simpleRoot C pc)
    (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
    (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p A)
    (actualPathWord_bounded Ω C coord hcoord pc e he S hS hcomp L hdeg p hp A) f
  refine ⟨coeff D g,?_⟩
  rw [actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p _ D A
    (le_max_left _ _) (le_max_right _ _),hg,coeff_map]
end
end ElementaryPositivity.RationalFiber

end

end OAI
