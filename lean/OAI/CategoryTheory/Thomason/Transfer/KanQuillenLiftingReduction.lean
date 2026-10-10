import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Simplicial.SingularCounitSurjectivity
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge

namespace OAI

section

/-! # The Kan–Quillen boundary-lifting implication

Goerss–Jardine (1999), Theorems I.11.3–I.11.4 and Corollary II.8.6 imply that a Kan fibration which
is a weak equivalence of actual realizations lifts against each boundary.
The implication identifies acyclic Kan fibrations with the boundary
right-lifting class.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.MorphismProperty SSet.modelCategoryQuillen

/-- The boundary-lifting consequence of Goerss–Jardine, Theorems
I.11.3–I.11.4; Corollary II.8.6 records properness. -/
abbrev PublishedAcyclicKanLifting : Prop :=
  J.rlp ⊓ realizationWeakEquivalences.{0} ≤ I.rlp

/-- The reverse anodyne implication follows by horn factorization and a concrete retract. -/
theorem anodyne_class_of_acyclic_kan_lifting (h : PublishedAcyclicKanLifting) :
    SSet.anodyneExtensions.{0} = monomorphisms SSet.{0} ⊓ realizationWeakEquivalences := by
  apply le_antisymm anodyne_mono_realization_weak
  intro X Y f hf
  let := horn_weakFactorizationSystem
  let d := factorizationData SSet.anodyneExtensions J.rlp f
  have hiw := anodyne_realization_weak d.i d.hi
  have hpw : realizationWeakEquivalences d.p := by
    apply realizationWeakEquivalences.of_precomp d.i d.p hiw
    simpa only [d.fac] using hf.2
  have hp : I.rlp d.p := h d.p ⟨d.hp, hpw⟩
  have hm : (monomorphisms SSet.{0}).rlp d.p := by rwa [SSet.rlp_monomorphisms]
  let : HasLiftingProperty f d.p := hm f hf.1
  let sq : CommSq d.i f d.p (𝟙 Y) := ⟨d.fac.trans (Category.comp_id f).symm⟩
  let r : RetractArrow f d.i := {
    i := Arrow.homMk (𝟙 X) sq.lift sq.fac_left.symm
    r := Arrow.homMk (𝟙 X) d.p ((Category.id_comp f).trans d.fac.symm)
    retract := by
      apply Arrow.hom_ext
      · simp
      · exact sq.fac_right }
  exact SSet.anodyneExtensions.of_retract r d.hi

/-- The trivial-fibration class equality follows from acyclic Kan lifting. -/
theorem boundary_class_of_acyclic_kan_lifting (h : PublishedAcyclicKanLifting) :
    I.rlp = J.rlp ⊓ realizationWeakEquivalences.{0} := by
  apply le_antisymm
  · intro X Y f hf
    have hm : (monomorphisms SSet.{0}).rlp f := by rwa [SSet.rlp_monomorphisms]
    exact ⟨antitone_rlp J_le_monomorphisms f hm, boundary_rlp_weak f hf⟩
  · exact h

/-- Acyclic Kan lifting supplies the Kan–Quillen model axioms. -/
theorem kanQuillenInput_of_acyclic_kan_lifting (h : PublishedAcyclicKanLifting) :
    KanQuillenPublishedInput.{0} :=
  kanQuillenInput_of_class_identifications (boundary_class_of_acyclic_kan_lifting h)
    (anodyne_class_of_acyclic_kan_lifting h)

end Thomason.Construction

end

end OAI
