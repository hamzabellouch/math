import Mathlib
import OAI.Algebra.GroupRing.SplitModel
import OAI.Algebra.GroupRing.ConcreteTorsion

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors
lemma HasFiniteTwoDimensionalClassifyingSpace.of_equiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (h : HasFiniteTwoDimensionalClassifyingSpace H) :
    HasFiniteTwoDimensionalClassifyingSpace G := by
  rcases h with ⟨X,topX,hT,hP,cw,hf,hh,h2,x,⟨k⟩,E,topE,hE,p,hp,hps⟩
  exact ⟨X,topX,hT,hP,cw,hf,hh,h2,x,⟨e.trans k⟩,E,topE,hE,p,hp,hps⟩
end TorsionFreeZeroDivisors
namespace TorsionFreeZeroDivisors.ConcreteModel
open scoped Classical
open SampleGraph
variable (rep : ℕ) (r : ActualPatternEvent.Match rep)
  (x : VA rep) (y : VB rep)
  (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
  (hsample : r∈ActualPatternEvent.samples rep)
  (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
    (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y))
include hL hd hsample havoid in
/-- The finite exact two-dimensional model of the actual sampled graph group.
The cover contraction is built by absorbing physical disk-track obstructions
through the proved integral cell-boundary splitting. -/
theorem has_model : HasFiniteTwoDimensionalClassifyingSpace (ConcreteGroup.G rep r) := by
  have hex {O : Type} [Fintype O] [Nonempty O]
      (a : SphericalPicture.Data (O:=O) (graph rep r) (ConcreteTorsion.signedLabels rep) WordPairing.inverseLetter) : ¬a.Reduced := by
    intro ha
    exact SpherePicture.excluded (ConcreteTorsion.unsigned rep r a) ha hL hd hsample havoid
  obtain ⟨t,ht⟩ := Finset.card_pos.mp (show 0<(Types.outgoingA x).card by
    have h := (Types.degreeA_bounds x).1
    omega)
  let : Nonempty (GraphConePresentation.Edge (graph rep r)) :=
    ⟨GraphConePresentation.edge (graph rep r) (Sum.inl ⟨(x,t),ht⟩)⟩
  have hm := RelationModel.has_model
    (ConeArea.words (graph rep r) (ConcreteGroup.routes rep r) (ConcreteTorsion.signedLabels rep))
    (ConeTorsion.total_zero (graph rep r) (ConcreteGroup.routes rep r) (ConcreteTorsion.signedLabels rep)
      (ConcreteTorsion.signedLabels_reverse rep r) hex)
  unfold RelationArea.G at hm
  rw [ConeTorsion.relations_eq _ _ _ (ConcreteTorsion.signedLabels_reverse rep r)] at hm
  rw [ConcreteTorsion.letters_eq] at hm
  exact HasFiniteTwoDimensionalClassifyingSpace.of_equiv
    (GraphConePresentation.equivalence (graph rep r) (ConcreteGroup.labels rep) (ConcreteGroup.routes rep r)
      (ConcreteGroup.labels_reverse rep r) (GraphConePresentation.canonical_base _)) hm
end TorsionFreeZeroDivisors.ConcreteModel

end

end OAI
