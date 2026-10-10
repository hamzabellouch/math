import Mathlib
import OAI.Algebra.GroupRing.TypedComponent
import OAI.Algebra.GroupRing.ConeTorsion

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ConcreteTorsion
open scoped Classical
open SampleGraph
variable (rep : ℕ) (r : ActualPatternEvent.Match rep)
def signedLabels : DA rep⊕DB rep→Types.Generator×Bool :=
  Types.signedLetter.symm ∘ label rep
lemma signedLabels_reverse (d : DA rep⊕DB rep) :
    signedLabels rep ((graph rep r).reverse d)=WordPairing.inverseLetter (signedLabels rep d) := by
  simp only [signedLabels,Function.comp_apply,label_reverse,Types.inverse,Equiv.symm_apply_apply]
  rfl
lemma freeLetter_eq (t : Types.Letter) :
    ConeSigned.freeLetter (Types.signedLetter.symm t)=ConcreteGroup.freeLetter t := by
  obtain ⟨⟨g,b⟩,rfl⟩ := Types.signedLetter.surjective t
  cases b <;> simp only [ConeSigned.freeLetter,ConcreteGroup.freeLetter,Equiv.symm_apply_apply,Bool.false_eq_true,ite_false,ite_true] <;> rfl
lemma letters_eq : ConeSigned.freeLetter ∘ signedLabels rep=ConcreteGroup.labels rep := by
  funext d
  exact freeLetter_eq _
def unsigned {O : Type} [Fintype O]
    (a : SphericalPicture.Data (O:=O) (graph rep r) (signedLabels rep) WordPairing.inverseLetter) :
    SphericalPicture.Data (O:=O) (graph rep r) (label rep) Types.inverse where
  rotation := a.rotation
  partner := a.partner
  involutive := a.involutive
  fixed_free := a.fixed_free
  dart := a.dart
  consistent := a.consistent
  compatible i := by
    have h := congrArg Types.signedLetter (a.compatible i)
    simpa only [signedLabels,Function.comp_apply,Equiv.apply_symm_apply,WordPairing.inverseLetter,Types.inverse] using h
  genusZero := a.genusZero
variable (x : VA rep) (y : VB rep)
  (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
  (hsample : r∈ActualPatternEvent.samples rep)
  (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
    (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y))
include hL hd hsample havoid in
theorem torsion_free : ∀ (g : ConcreteGroup.G rep r) (n : ℕ), 0 < n → g ^ n = 1 → g = 1 := by
  have hex {O : Type} [Fintype O] [Nonempty O]
      (a : SphericalPicture.Data (O:=O) (graph rep r) (signedLabels rep) WordPairing.inverseLetter) : ¬a.Reduced := by
    intro ha
    exact SpherePicture.excluded (unsigned rep r a) ha hL hd hsample havoid
  have h := ConeTorsion.graph_torsion_free (graph rep r) (ConcreteGroup.routes rep r)
    (signedLabels rep) (signedLabels_reverse rep r) (GraphConePresentation.canonical_base _) hex
  rw [letters_eq] at h
  exact h
end TorsionFreeZeroDivisors.ConcreteTorsion

namespace TorsionFreeZeroDivisors
/-- The exact group's ordinary torsion-freeness and both nonzero zero-divisor
factors, proved without assuming a resolution or topological asphericity. The
finite classifying-space clause remains separate and is not asserted here. -/
theorem torsion_free_finitely_presented_zero_divisors :
    ∃ (G : Type) (inst : Group G), letI : Group G := inst
      Group.IsFinitelyPresented G ∧
      (∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1) ∧
      ∃ α β : MonoidAlgebra (ZMod 2) G, α≠0 ∧ β≠0 ∧ α*β=0 := by
  obtain ⟨rep,r,x,y,hr,hL,hd,ha,hx,hy,hz⟩ := SampleGraph.exists_nonzero_factors
  exact ⟨ConcreteGroup.G rep r,inferInstance,inferInstance,
    ConcreteTorsion.torsion_free rep r x y hL hd hr ha,
    ConcreteFactors.alpha rep r x,ConcreteFactors.beta rep r y,hx,hy,hz⟩
end TorsionFreeZeroDivisors

end

end OAI
