import Mathlib
import OAI.Algebra.GroupRing.PlanarMap

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedComponent
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings TypedGraphs
variable {V : Type} (outgoing : V→Finset Types.Letter)
    (r : Matching (label outgoing) Types.inverse) (root : V)
abbrev graph := r.graph (origin outgoing)
abbrev Vertex := {v : V // (ShortClosure.simpleGraph (graph outgoing r)).Reachable root v}
def out (v : Vertex outgoing r root) : Finset Types.Letter := outgoing v.val
abbrev Dart := Factors.DartA (out outgoing r root)
def lift (d : Dart outgoing r root) : TypedGraphs.Dart outgoing :=
  ⟨(d.val.1.val,d.val.2),d.property⟩
lemma lift_injective : Function.Injective (lift outgoing r root) := by
  intro d e h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z : TypedGraphs.Dart outgoing => z.val.1) h
  · exact congrArg (fun z : TypedGraphs.Dart outgoing => z.val.2) h

def reverse (d : Dart outgoing r root) : Dart outgoing r root :=
  ⟨(⟨(r (lift outgoing r root d)).val.1,
    d.val.1.property.trans (ShortClosure.dart_reachable (graph outgoing r) (lift outgoing r root d))⟩,
    (r (lift outgoing r root d)).val.2),(r (lift outgoing r root d)).property⟩
lemma lift_reverse (d : Dart outgoing r root) :
    lift outgoing r root (reverse outgoing r root d)=r (lift outgoing r root d) := rfl
lemma reverse_reverse : Function.Involutive (reverse outgoing r root) := by
  intro d
  apply lift_injective outgoing r root
  rw [lift_reverse,lift_reverse,r.reverse_reverse]
lemma label_reverse (d : Dart outgoing r root) :
    (reverse outgoing r root d).val.2=Types.inverse d.val.2 :=
  r.label_reverse (lift outgoing r root d)
def base : Vertex outgoing r root := ⟨root,.refl _⟩
end TorsionFreeZeroDivisors.TypedComponent

namespace TorsionFreeZeroDivisors.ComponentFactors
open scoped Classical BigOperators
open ConditionedMatchings TypedGraphs TypedComponent SampleGraph
variable {G : Type} [Group G] (rep : ℕ) (r : ActualPatternEvent.Match rep)
  (x : SampleGraph.VA rep) (y : SampleGraph.VB rep)
abbrev CA := TypedComponent.Vertex (@Types.outgoingA rep) r.1 x
abbrev CB := TypedComponent.Vertex (@Types.outgoingB rep) r.2 y
/-- Actual full components in the chosen sample, with every outgoing edge
retained. Parallel simultaneous steps cancel as distinct signed flags. -/
theorem product_zero (letter : Types.Letter→G) (g : CA rep r x→G) (h : CB rep r y→G)
    (hg : ∀ d : TypedComponent.Dart (@Types.outgoingA rep) r.1 x,
      g (TypedComponent.reverse _ r.1 x d).val.1=g d.val.1*letter d.val.2)
    (hh : ∀ d : TypedComponent.Dart (@Types.outgoingB rep) r.2 y,
      h (TypedComponent.reverse _ r.2 y d).val.1=h d.val.1*letter d.val.2) :
    (∑ a,MonoidAlgebra.single (g a) (1 : ZMod 2)) *
      (∑ b,MonoidAlgebra.single ((h b)⁻¹) (1 : ZMod 2))=0 := by
  exact Factors.product_zero (TypedComponent.out _ r.1 x) (TypedComponent.out _ r.2 y)
    Types.inverse (TypedComponent.reverse _ r.1 x) (TypedComponent.reverse _ r.2 y)
    (TypedComponent.label_reverse _ r.1 x) (TypedComponent.label_reverse _ r.2 y)
    (TypedComponent.reverse_reverse _ r.1 x) (TypedComponent.reverse_reverse _ r.2 y)
    Types.inverse_ne (fun leftVertex rightVertex => by
      convert Types.odd_cross_intersections leftVertex.val rightVertex.val using 1
      congr 1
      ext letterType
      simp [TypedComponent.out]) letter g h hg hh

/-- Given the source's root nontriviality endpoint, these very sums are the
nonzero factors. No pairwise distinctness of the other vertex labels is used. -/
theorem nonzero_factors
    (letter : Types.Letter→G) (g : CA rep r x→G) (h : CB rep r y→G)
    (hg : ∀ d : TypedComponent.Dart (@Types.outgoingA rep) r.1 x,
      g (TypedComponent.reverse _ r.1 x d).val.1=g d.val.1*letter d.val.2)
    (hh : ∀ d : TypedComponent.Dart (@Types.outgoingB rep) r.2 y,
      h (TypedComponent.reverse _ r.2 y d).val.1=h d.val.1*letter d.val.2)
    (hx : g (TypedComponent.base _ r.1 x)=1) (hy : h (TypedComponent.base _ r.2 y)=1)
    (hux : ∀ a,g a=1 → a=TypedComponent.base _ r.1 x)
    (huy : ∀ b,h b=1 → b=TypedComponent.base _ r.2 y) :
    ∃ α β : MonoidAlgebra (ZMod 2) G,α≠0 ∧ β≠0 ∧ α*β=0 := by
  refine ⟨∑ a,MonoidAlgebra.single (g a) 1,∑ b,MonoidAlgebra.single ((h b)⁻¹) 1,
    Factors.sum_nonzero _ g hx hux,?_,product_zero rep r x y letter g h hg hh⟩
  apply Factors.sum_nonzero (TypedComponent.base _ r.2 y) (fun b => (h b)⁻¹)
  · simp only [hy,inv_one]
  · intro b hb
    exact huy b (inv_eq_one.mp hb)
end TorsionFreeZeroDivisors.ComponentFactors

namespace TorsionFreeZeroDivisors.ConcreteFactors
open scoped Classical BigOperators
open TypedGraphs ConditionedMatchings SampleGraph ConcreteGroup TypedComponent
variable (rep : ℕ) (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep)
def leftValue (a : ComponentFactors.CA rep r x) : G rep r :=
  (value rep r (Sum.inl x))⁻¹*value rep r (Sum.inl a.val)
def rightValue (b : ComponentFactors.CB rep r y) : G rep r :=
  (value rep r (Sum.inr y))⁻¹*value rep r (Sum.inr b.val)
lemma left_edge (d : TypedComponent.Dart (@Types.outgoingA rep) r.1 x) :
    leftValue rep r x (TypedComponent.reverse _ r.1 x d).val.1=
      leftValue rep r x d.val.1*letter rep r d.val.2 := by
  have h := ConcreteGroup.edge rep r (Sum.inl (TypedComponent.lift _ r.1 x d))
  change value rep r (Sum.inl (r.1 (TypedComponent.lift _ r.1 x d)).val.1)=
    value rep r (Sum.inl d.val.1.val)*letter rep r d.val.2 at h
  change (value rep r (Sum.inl x))⁻¹*value rep r (Sum.inl (r.1 (TypedComponent.lift _ r.1 x d)).val.1)=_
  rw [h]
  exact (mul_assoc _ _ _).symm
lemma right_edge (d : TypedComponent.Dart (@Types.outgoingB rep) r.2 y) :
    rightValue rep r y (TypedComponent.reverse _ r.2 y d).val.1=
      rightValue rep r y d.val.1*letter rep r d.val.2 := by
  have h := ConcreteGroup.edge rep r (Sum.inr (TypedComponent.lift _ r.2 y d))
  change value rep r (Sum.inr (r.2 (TypedComponent.lift _ r.2 y d)).val.1)=
    value rep r (Sum.inr d.val.1.val)*letter rep r d.val.2 at h
  change (value rep r (Sum.inr y))⁻¹*value rep r (Sum.inr (r.2 (TypedComponent.lift _ r.2 y d)).val.1)=_
  rw [h]
  exact (mul_assoc _ _ _).symm
@[simp] lemma left_root : leftValue rep r x (TypedComponent.base _ r.1 x)=1 := by
  simp [leftValue,TypedComponent.base]
@[simp] lemma right_root : rightValue rep r y (TypedComponent.base _ r.2 y)=1 := by
  simp [rightValue,TypedComponent.base]
def alpha : MonoidAlgebra (ZMod 2) (G rep r) :=
  ∑ a,MonoidAlgebra.single (leftValue rep r x a) 1
def beta : MonoidAlgebra (ZMod 2) (G rep r) :=
  ∑ b,MonoidAlgebra.single ((rightValue rep r y b)⁻¹) 1
/-- The author's factors multiply to zero in the exact finite graph presentation,
for every matching sample. Nonvanishing is a separate geometric obligation. -/
theorem product_zero : alpha rep r x*beta rep r y=0 :=
  ComponentFactors.product_zero rep r x y (letter rep r) (leftValue rep r x) (rightValue rep r y)
    (left_edge rep r x) (right_edge rep r y)
lemma alpha_nonzero
    (hroot : ∀ a,leftValue rep r x a=1 → a=TypedComponent.base _ r.1 x) :
    alpha rep r x≠0 :=
  Factors.sum_nonzero _ (leftValue rep r x) (left_root rep r x) hroot
lemma beta_nonzero
    (hroot : ∀ b,rightValue rep r y b=1 → b=TypedComponent.base _ r.2 y) :
    beta rep r y≠0 := by
  apply Factors.sum_nonzero (TypedComponent.base _ r.2 y) (fun b => (rightValue rep r y b)⁻¹)
  · simp
  · intro b hb
    exact hroot b (inv_eq_one.mp hb)
end TorsionFreeZeroDivisors.ConcreteFactors

namespace TorsionFreeZeroDivisors.SumPort
open scoped Classical
open PortSubdivision
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
def leftHom : ShortClosure.simpleGraph A →g ShortClosure.simpleGraph (graph A B) where
  toFun := Sum.inl
  map_rel' := by
    rintro a b ⟨hab,d,ha,hb⟩
    exact ⟨fun h=>hab (Sum.inl.inj h),Sum.inl d,congrArg Sum.inl ha,congrArg Sum.inl hb⟩
def rightHom : ShortClosure.simpleGraph B →g ShortClosure.simpleGraph (graph A B) where
  toFun := Sum.inr
  map_rel' := by
    rintro a b ⟨hab,d,ha,hb⟩
    exact ⟨fun h=>hab (Sum.inr.inj h),Sum.inr d,congrArg Sum.inr ha,congrArg Sum.inr hb⟩
end TorsionFreeZeroDivisors.SumPort
namespace TorsionFreeZeroDivisors.ConcreteFactors

section
open scoped Classical
open SampleGraph ConcreteGroup
variable {rep : ℕ} (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep)
  (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
  (hsample : r∈ActualPatternEvent.samples rep)
  (hsep : Picture.SeparatorObligation r x y hL hd)
  (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
    (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y))
include hsample hsep havoid
/-- Source disk nontriviality suffices for the literal left factor, without
assuming distinctness of the other vertex values. The sharp separator is the
explicit still-unclosed premise, not an axiom or a claim of the main theorem. -/
theorem alpha_nonzero_of_separator : alpha rep r x≠0 := by
  apply alpha_nonzero rep r x
  intro a ha
  apply Subtype.ext
  by_contra hn
  have hp := a.property.map (SumPort.leftHom (A rep r) (B rep r))
  have he : value rep r (Sum.inl x)=value rep r (Sum.inl a.val) := by
    have ha' : (value rep r (Sum.inl x))⁻¹*value rep r (Sum.inl a.val)=1 := ha
    exact inv_mul_eq_one.mp ha'
  obtain ⟨n,b,hb⟩ := equal_value_picture r hp
    (fun he=>hn (Sum.inl.inj he).symm) he
  exact Picture.excluded b (fun he=>hn (Sum.inl.inj he).symm) hb (Or.inl rfl)
    hL hd hsample (hsep _ _ n b _ hb (Or.inl rfl)) havoid
/-- The right factor's identity coefficient is likewise exactly one; its
inversion does not require a global component embedding theorem. -/
theorem beta_nonzero_of_separator : beta rep r y≠0 := by
  apply beta_nonzero rep r y
  intro a ha
  apply Subtype.ext
  by_contra hn
  have hp := a.property.map (SumPort.rightHom (A rep r) (B rep r))
  have he : value rep r (Sum.inr y)=value rep r (Sum.inr a.val) := by
    have ha' : (value rep r (Sum.inr y))⁻¹*value rep r (Sum.inr a.val)=1 := ha
    exact inv_mul_eq_one.mp ha'
  obtain ⟨n,b,hb⟩ := equal_value_picture r hp
    (fun he=>hn (Sum.inr.inj he).symm) he
  exact Picture.excluded b (fun he=>hn (Sum.inr.inj he).symm) hb (Or.inr rfl)
    hL hd hsample (hsep _ _ n b _ hb (Or.inr rfl)) havoid

end
open scoped Classical
open SampleGraph
variable {rep : ℕ} (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep)
  (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
  (hsample : r∈ActualPatternEvent.samples rep)
  (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
    (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y))
include hL hd hsample havoid
/-- Both original factors are now unconditionally nonzero for the sampled
no-arrangement graphs. The literal sharp separator is proved, not assumed. -/
theorem both_nonzero : alpha rep r x≠0 ∧ beta rep r y≠0 := by
  have hs := Picture.separator_obligation r x y hL hd
  exact ⟨alpha_nonzero_of_separator r x y hL hd hsample hs havoid,
    beta_nonzero_of_separator r x y hL hd hsample hs havoid⟩
end TorsionFreeZeroDivisors.ConcreteFactors

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical
open Filter GirthAsymptotics TypedGraphs
/-- An actual sample with both nonzero factors in its exact finitely presented
group. Torsion-freeness and the topological classifying-space clause are NOT
asserted here; they remain obligations for the main theorem. -/
theorem exists_nonzero_factors :
    ∃ (rep : ℕ) (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep),
      r∈ActualPatternEvent.samples rep ∧ 2≤L (size rep) ∧
      GraphSample.Diameters rep r ∧
      IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
        (PlanarParameters.K PathSystem.ε ClosedWords.D)
        (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y) ∧
      ConcreteFactors.alpha rep r x≠0 ∧ ConcreteFactors.beta rep r y≠0 ∧
      ConcreteFactors.alpha rep r x*ConcreteFactors.beta rep r y=0 := by
  have he := exists_avoiding (PlanarParameters.C PathSystem.ε ClosedWords.D)
    (PlanarParameters.K PathSystem.ε ClosedWords.D)
    (PlanarParameters.sides PathSystem.ε ClosedWords.D)
    (PlanarParameters.K_pos _ _) (PlanarParameters.sides_pos _ _)
  have hL := (L_tendsto.comp size_tendsto).eventually (eventually_ge_atTop 2)
  obtain ⟨rep,hrep,hL,hpos⟩ := (he.and (hL.and (eventually_ge_atTop 1))).exists
  let : NeZero rep := ⟨by omega⟩
  let x : VA rep := Classical.choice inferInstance
  let y : VB rep := Classical.choice inferInstance
  obtain ⟨r,hr,hd,ha⟩ := hrep x y
  obtain ⟨hx,hy⟩ := ConcreteFactors.both_nonzero r x y hL hd hr ha
  exact ⟨rep,r,x,y,hr,hL,hd,ha,hx,hy,ConcreteFactors.product_zero rep r x y⟩
end TorsionFreeZeroDivisors.SampleGraph

namespace TorsionFreeZeroDivisors
/-- Complete algebraic zero-divisor part of the construction, without the
still-missing ordinary torsion-free and finite K(G,1) conclusions. -/
theorem finitely_presented_zero_divisors :
    ∃ (G : Type) (inst : Group G), letI : Group G := inst
      Group.IsFinitelyPresented G ∧
      ∃ α β : MonoidAlgebra (ZMod 2) G, α≠0 ∧ β≠0 ∧ α*β=0 := by
  obtain ⟨rep,r,x,y,_,_,_,_,hx,hy,hz⟩ := SampleGraph.exists_nonzero_factors
  exact ⟨ConcreteGroup.G rep r,inferInstance,inferInstance,
    ConcreteFactors.alpha rep r x,ConcreteFactors.beta rep r y,hx,hy,hz⟩
end TorsionFreeZeroDivisors

end

end OAI
