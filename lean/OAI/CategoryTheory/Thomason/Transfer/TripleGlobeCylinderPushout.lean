import OAI.CategoryTheory.Thomason.Gray.TopologicalConePrism
import OAI.CategoryTheory.Thomason.Gray.TripleGlobeCylinderSource
import OAI.CategoryTheory.Thomason.Simplicial.TopologicalDeformationTransport
import OAI.CategoryTheory.Thomason.Transfer.HornAttachmentWeakEquivalences
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

namespace OAI

section

/-! # Simultaneous horn attachments

Realization transports the coproduct deformation through its canonical
coproduct comparison isomorphisms. Arbitrary simultaneous horn attachments
therefore satisfy the actual realization weak-equivalence test.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

/-- Actual realization of a coproduct inherits the componentwise deformations. -/
def realizedCoproductData {α : Type} {A B : α → SSet.{0}} (f : ∀ a, A a ⟶ B a)
    (d : ∀ a, TopologicalDeformation.Data (SSet.toTop.map (f a))) :
    TopologicalDeformation.Data (SSet.toTop.map (CategoryTheory.Limits.Sigma.map f)) :=
  (TopologicalDeformation.coproductData (fun a => SSet.toTop.obj (A a))
    (fun a => SSet.toTop.obj (B a)) (fun a => SSet.toTop.map (f a)) d).ofIso
      (PreservesCoproduct.iso SSet.toTop A).symm
      (PreservesCoproduct.iso SSet.toTop B).symm (by
        change CategoryTheory.Limits.Sigma.map (fun a => SSet.toTop.map (f a)) ≫
          sigmaComparison SSet.toTop B =
          sigmaComparison SSet.toTop A ≫ SSet.toTop.map (CategoryTheory.Limits.Sigma.map f)
        apply Sigma.hom_ext
        intro a
        rw [← Category.assoc, Sigma.ι_map, Category.assoc, ι_comp_sigmaComparison]
        rw [← Category.assoc, ι_comp_sigmaComparison]
        rw [← SSet.toTop.map_comp (Sigma.ι A a) (CategoryTheory.Limits.Sigma.map f), Sigma.ι_map]
        exact (SSet.toTop.map_comp (f a) (Sigma.ι B a)).symm)

/-- A coproduct of generating horns has a stationary realized deformation. -/
def simultaneousHornData {α : Type} (n : α → ℕ) (i : ∀ a, Fin (n a+2)) :
    TopologicalDeformation.Data (SSet.toTop.map
      (CategoryTheory.Limits.Sigma.map (fun a =>
        (Λ[n a+1, i a].ι : _ ⟶ (Δ[n a+1] : SSet.{0}))))) :=
  realizedCoproductData _ (fun a => realizedHornData (i a))

/-- Attaching any family of horns at once is an actual realization weak equivalence. -/
theorem simultaneous_horn_attachment_weak {α : Type} (n : α → ℕ) (i : ∀ a, Fin (n a+2))
    {X P : SSet.{0}}
    {f : (∐ fun a => (Λ[n a+1, i a] : SSet.{0})) ⟶ X}
    {b : (∐ fun a => (Δ[n a+1] : SSet.{0})) ⟶ P} {j : X ⟶ P}
    (h : IsPushout (CategoryTheory.Limits.Sigma.map
      (fun a => (Λ[n a+1, i a].ι : _ ⟶ (Δ[n a+1] : SSet.{0})))) f b j) :
    realizationWeakEquivalences j :=
  TopologicalDeformation.pushout_weak (SSet.toTop.map_isPushout h) (simultaneousHornData n i)

end

end Thomason.Construction

end

section

/-! # Actual preservation of the triple-globe pushout by the chain cylinder -/

namespace Thomason.Construction.StrictOmegaCategory.TripleGlobeCylinder

open CategoryTheory CategoryTheory.Limits _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

private theorem generated_image {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)
    {D : StrictOmegaCategory.{0}} {I : Type} (g : I → D) (F : K.realization ⟶ D)
    (ha : ∀ p b, Nonempty (CompositionExpression D g (F.toFun (B.atom p b))))
    (x : K.realization) : Nonempty (CompositionExpression D g (F.toFun x)) := by
  apply B.generated (fun x => Nonempty (CompositionExpression D g (F.toFun x))) ha _ x
  intro r u v huv hu hv
  have hm : D.target r (F.toFun u) = D.source r (F.toFun v) :=
    (F.map_face true r u).symm.trans ((congrArg F.toFun huv).trans (F.map_face false r v))
  change Nonempty (CompositionExpression D g (F.toFun (Cell.comp u v r huv)))
  obtain ⟨tu⟩ := hu
  obtain ⟨tv⟩ := hv
  exact (F.map_comp r u v huv hm).symm ▸ ⟨CompositionExpression.comp r hm tu tv⟩

theorem pair_basisComparison {n k : ℕ} (hkn : k < n) :
    pushout.inl (model.map (TripleGlobe.bridge n k)) (model.map (Globe.faceMap false k n)) ≫
      basisComparison hkn = (PastingGlobeCylinderBasis.modelIso hkn).hom ≫
        (RightCylinder.map (TripleGlobeBasis.pairInclusion hkn)).realization := by
  rw [basisComparison, ← Category.assoc, inl_comparison, TripleGlobeBasis.model_pair]

theorem last_basisComparison {n k : ℕ} (hkn : k < n) :
    pushout.inr (model.map (TripleGlobe.bridge n k)) (model.map (Globe.faceMap false k n)) ≫
      basisComparison hkn = (TripleGlobeBasis.globeModelIso n).hom ≫
        (RightCylinder.map (TripleGlobeBasis.inclusion hkn 2)).realization := by
  rw [basisComparison, ← Category.assoc, inr_comparison, TripleGlobeBasis.model_globe]

theorem pair_atom_eq_lift {n k p : ℕ} (hkn : k < n)
    (b : PastingGlobeCylinderBasis.Basis n k p) :
    TripleGlobe.imageCell model n k (.inl ((PastingGlobeCylinderBasis.modelIso hkn).inv.toFun
      (PastingGlobeCylinderBasis.atom hkn b))) =
      atomLift hkn ⟨p, TripleGlobeBasis.pairCylinderIndex hkn b⟩ := by
  apply imageCell_eq_of_basisComparison hkn
  have he := congrArg (fun F => F.toFun ((PastingGlobeCylinderBasis.modelIso hkn).inv.toFun
    (PastingGlobeCylinderBasis.atom hkn b))) (pair_basisComparison hkn)
  have hi := congrArg (fun F => F.toFun (PastingGlobeCylinderBasis.atom hkn b))
    (PastingGlobeCylinderBasis.modelIso hkn).inv_hom_id
  exact he.trans ((congrArg
    (RightCylinder.map (TripleGlobeBasis.pairInclusion hkn)).realization.toFun hi).trans
      ((TripleGlobeBasis.pairCylinder_atom hkn b).trans (atomLift_image hkn
        ⟨p, TripleGlobeBasis.pairCylinderIndex hkn b⟩).symm))

theorem last_atom_eq_lift {n k p : ℕ} (hkn : k < n)
    (b : (DirectedGlobeComplex.cylinderOrderedAtomBasis n).Index p) :
    TripleGlobe.imageCell model n k (.inr ((TripleGlobeBasis.globeModelIso n).inv.toFun
      ((DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom p b))) =
      atomLift hkn ⟨p, TripleGlobeBasis.globeCylinderIndex hkn 2 b⟩ := by
  apply imageCell_eq_of_basisComparison hkn
  have he := congrArg (fun F => F.toFun ((TripleGlobeBasis.globeModelIso n).inv.toFun
    ((DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom p b))) (last_basisComparison hkn)
  have hi := congrArg (fun F => F.toFun
    ((DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom p b))
    (TripleGlobeBasis.globeModelIso n).inv_hom_id
  exact he.trans ((congrArg
    (RightCylinder.map (TripleGlobeBasis.inclusion hkn 2)).realization.toFun hi).trans
      ((TripleGlobeBasis.globeCylinder_atom hkn 2 b).trans (atomLift_image hkn
        ⟨p, TripleGlobeBasis.globeCylinderIndex hkn 2 b⟩).symm))

theorem pair_generated {n k : ℕ} (hkn : k < n)
    (x : model.obj (PastingGlobe.category n n k)) :
    Nonempty (CompositionExpression (Source n k) (atomLift hkn)
      (TripleGlobe.imageCell model n k (.inl x))) := by
  let F : (PastingGlobeCylinderBasis.Cylinder hkn).realization ⟶ Source n k :=
    (PastingGlobeCylinderBasis.modelIso hkn).inv ≫ pushout.inl _ _
  have h := generated_image (PastingGlobeCylinderBasis.orderedAtomBasis hkn) (atomLift hkn) F
    (fun p b => by
      change PastingGlobeCylinderBasis.Basis n k p at b
      change Nonempty (CompositionExpression (Source n k) (atomLift hkn)
        (TripleGlobe.imageCell model n k (.inl ((PastingGlobeCylinderBasis.modelIso hkn).inv.toFun
          (PastingGlobeCylinderBasis.atom hkn b)))))
      rw [pair_atom_eq_lift hkn b]
      exact ⟨CompositionExpression.generator (C := Source n k) (g := atomLift hkn)
        (⟨p, TripleGlobeBasis.pairCylinderIndex hkn b⟩ : (atomBasis hkn).AtomIndex)⟩)
    ((PastingGlobeCylinderBasis.modelIso hkn).hom.toFun x)
  have hi := congrArg (fun G => G.toFun x) (PastingGlobeCylinderBasis.modelIso hkn).hom_inv_id
  change (PastingGlobeCylinderBasis.modelIso hkn).inv.toFun
    ((PastingGlobeCylinderBasis.modelIso hkn).hom.toFun x) = x at hi
  change Nonempty (CompositionExpression (Source n k) (atomLift hkn)
    (TripleGlobe.imageCell model n k (.inl ((PastingGlobeCylinderBasis.modelIso hkn).inv.toFun
      ((PastingGlobeCylinderBasis.modelIso hkn).hom.toFun x))))) at h
  rw [hi] at h
  exact h

theorem last_generated {n k : ℕ} (hkn : k < n) (x : model.obj (Globe.category n)) :
    Nonempty (CompositionExpression (Source n k) (atomLift hkn)
      (TripleGlobe.imageCell model n k (.inr x))) := by
  let F : (rightCylinder (DirectedGlobeComplex.complex n)).realization ⟶ Source n k :=
    (TripleGlobeBasis.globeModelIso n).inv ≫ pushout.inr _ _
  have h := generated_image (DirectedGlobeComplex.cylinderOrderedAtomBasis n) (atomLift hkn) F
    (fun p b => by
      change Nonempty (CompositionExpression (Source n k) (atomLift hkn)
        (TripleGlobe.imageCell model n k (.inr ((TripleGlobeBasis.globeModelIso n).inv.toFun
          ((DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom p b)))))
      rw [last_atom_eq_lift hkn b]
      exact ⟨CompositionExpression.generator (C := Source n k) (g := atomLift hkn)
        (⟨p, TripleGlobeBasis.globeCylinderIndex hkn 2 b⟩ : (atomBasis hkn).AtomIndex)⟩)
    ((TripleGlobeBasis.globeModelIso n).hom.toFun x)
  have hi := congrArg (fun G => G.toFun x) (TripleGlobeBasis.globeModelIso n).hom_inv_id
  change (TripleGlobeBasis.globeModelIso n).inv.toFun
    ((TripleGlobeBasis.globeModelIso n).hom.toFun x) = x at hi
  change Nonempty (CompositionExpression (Source n k) (atomLift hkn)
    (TripleGlobe.imageCell model n k (.inr ((TripleGlobeBasis.globeModelIso n).inv.toFun
      ((TripleGlobeBasis.globeModelIso n).hom.toFun x))))) at h
  rw [hi] at h
  exact h

theorem generated {n k : ℕ} (hkn : k < n) (x : Source n k) :
    Nonempty (CompositionExpression (Source n k) (atomLift hkn) x) := by
  obtain ⟨t⟩ := PushoutGeneration.generated_by_pieces
    (model.map (TripleGlobe.bridge n k)) (model.map (Globe.faceMap false k n)) x
  exact t.substitute (𝟙 (Source n k)) (fun a => by
    cases a with
    | inl y => exact pair_generated hkn y
    | inr y => exact last_generated hkn y)

def basisIso {n k : ℕ} (hkn : k < n) :
    Source n k ≅ (rightCylinder (TripleGlobeBasis.complex n k hkn)).realization :=
  (atomBasis hkn).comparisonIso (atomLift hkn) (basisComparison hkn)
    (atomLift_image hkn) (atomLift_dimension hkn) (generated hkn)

def modelIso {n k : ℕ} (hkn : k < n) :
    Source n k ≅ model.obj (TripleGlobe.category n k) :=
  basisIso hkn ≪≫ (TripleGlobeBasis.modelIso hkn).symm

@[simp] theorem modelIso_hom {n k : ℕ} (hkn : k < n) :
    (modelIso hkn).hom = comparison n k := by
  change basisComparison hkn ≫ (TripleGlobeBasis.modelIso hkn).inv = _
  simp only [basisComparison, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem isPushout {n k : ℕ} (hkn : k < n) :
    IsPushout (model.map (TripleGlobe.bridge n k)) (model.map (Globe.faceMap false k n))
      (model.map (TripleGlobe.pair n k)) (model.map (TripleGlobe.inclusion n k 2)) := by
  apply IsPushout.of_iso_pushout
    (⟨by
      rw [← model.map_comp, ← model.map_comp]
      exact congrArg model.map (pushout.condition (f := TripleGlobe.bridge n k)
        (g := Globe.faceMap false k n))⟩) (modelIso hkn).symm
  · have he : pushout.inl (model.map (TripleGlobe.bridge n k))
        (model.map (Globe.faceMap false k n)) ≫ (modelIso hkn).hom =
        model.map (TripleGlobe.pair n k) := by
      rw [modelIso_hom]
      exact inl_comparison n k
    rw [← he, Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]
  · have he : pushout.inr (model.map (TripleGlobe.bridge n k))
        (model.map (Globe.faceMap false k n)) ≫ (modelIso hkn).hom =
        model.map (TripleGlobe.inclusion n k 2) := by
      rw [modelIso_hom]
      exact inr_comparison n k
    rw [← he, Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]

end
end Thomason.Construction.StrictOmegaCategory.TripleGlobeCylinder

end

end OAI
