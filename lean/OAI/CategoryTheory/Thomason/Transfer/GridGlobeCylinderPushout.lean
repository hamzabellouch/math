import OAI.CategoryTheory.Thomason.Gray.PrismSimplexNaturality
import OAI.CategoryTheory.Thomason.Gray.TopologicalConePrism

namespace OAI

section

/-! # The actual chain-cylinder model preserves the interchange pushout -/

namespace Thomason.Construction.StrictOmegaCategory.GridGlobeCylinder

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

theorem row_atom_eq_lift {n k l p : ℕ} (hkl : k < l) (hln : l < n) (s : Bool)
    (b : PastingGlobeCylinderBasis.Basis n k p) :
    (rowMap hkl s).toFun ((PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).inv.toFun
      (PastingGlobeCylinderBasis.atom (hkl.trans hln) b)) =
        atomLift hkl hln ⟨p, GridGlobeBasis.rowCylinderIndex hkl hln s b⟩ := by
  apply row_image_eq_of_basisComparison hkl hln
  have he := congrArg (fun F => F.toFun
    ((PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).inv.toFun
      (PastingGlobeCylinderBasis.atom (hkl.trans hln) b))) (rowMap_basisComparison hkl hln s)
  have hi := congrArg (fun F => F.toFun (PastingGlobeCylinderBasis.atom (hkl.trans hln) b))
    (PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).inv_hom_id
  exact he.trans ((congrArg (RightCylinder.map (GridGlobeBasis.inclusion hkl hln s)).realization.toFun hi).trans
    ((GridGlobeBasis.rowCylinder_atom hkl hln s b).trans
      (atomLift_image hkl hln ⟨p, GridGlobeBasis.rowCylinderIndex hkl hln s b⟩).symm))

theorem row_generated {n k l : ℕ} (hkl : k < l) (hln : l < n) (s : Bool)
    (x : model.obj (PastingGlobe.category n n k)) :
    Nonempty (CompositionExpression (Source (n := n) hkl) (atomLift hkl hln) ((rowMap hkl s).toFun x)) := by
  let F : (PastingGlobeCylinderBasis.Cylinder (hkl.trans hln)).realization ⟶ Source (n := n) hkl :=
    (PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).inv ≫ rowMap hkl s
  have h := generated_image (PastingGlobeCylinderBasis.orderedAtomBasis (hkl.trans hln))
    (atomLift hkl hln) F (fun p b => by
      change PastingGlobeCylinderBasis.Basis n k p at b
      change Nonempty (CompositionExpression (Source (n := n) hkl) (atomLift hkl hln)
        ((rowMap hkl s).toFun ((PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).inv.toFun
          (PastingGlobeCylinderBasis.atom (hkl.trans hln) b))))
      rw [row_atom_eq_lift hkl hln s b]
      exact ⟨CompositionExpression.generator (C := Source (n := n) hkl) (g := atomLift hkl hln)
        (⟨p, GridGlobeBasis.rowCylinderIndex hkl hln s b⟩ : (atomBasis hkl hln).AtomIndex)⟩)
    ((PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).hom.toFun x)
  have hi := congrArg (fun G => G.toFun x)
    (PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).hom_inv_id
  change (PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).inv.toFun
    ((PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).hom.toFun x) = x at hi
  change Nonempty (CompositionExpression (Source (n := n) hkl) (atomLift hkl hln)
    ((rowMap hkl s).toFun ((PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).inv.toFun
      ((PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).hom.toFun x)))) at h
  rw [hi] at h
  exact h

theorem generated {n k l : ℕ} (hkl : k < l) (hln : l < n) (x : Source (n := n) hkl) :
    Nonempty (CompositionExpression (Source (n := n) hkl) (atomLift hkl hln) x) := by
  obtain ⟨t⟩ := PushoutGeneration.generated_by_pieces
    (model.map (GrayMapping.pastingFace true l n k hkl))
    (model.map (GrayMapping.pastingFace false l n k hkl)) x
  exact t.substitute (𝟙 (Source (n := n) hkl)) (fun a => by
    cases a with
    | inl y => exact row_generated hkl hln false y
    | inr y => exact row_generated hkl hln true y)

def basisIso {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    Source (n := n) hkl ≅ (rightCylinder (GridGlobeBasis.complex hkl hln)).realization :=
  (atomBasis hkl hln).comparisonIso (atomLift hkl hln) (basisComparison hkl hln)
    (atomLift_image hkl hln) (atomLift_dimension hkl hln) (generated hkl hln)

def modelIso {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    Source (n := n) hkl ≅ model.obj (GridGlobe.category n k l hkl) :=
  basisIso hkl hln ≪≫ (GridGlobeBasis.modelIso hkl hln).symm

@[simp] theorem modelIso_hom {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    (modelIso hkl hln).hom = comparison hkl := by
  change basisComparison hkl hln ≫ (GridGlobeBasis.modelIso hkl hln).inv = _
  simp only [basisComparison, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem isPushout {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    IsPushout (model.map (GrayMapping.pastingFace true l n k hkl))
      (model.map (GrayMapping.pastingFace false l n k hkl))
      (model.map (GridGlobe.row n k l hkl false))
      (model.map (GridGlobe.row n k l hkl true)) := by
  apply IsPushout.of_iso_pushout
    (⟨by
      rw [← model.map_comp, ← model.map_comp]
      exact congrArg model.map (pushout.condition
        (f := GrayMapping.pastingFace true l n k hkl)
        (g := GrayMapping.pastingFace false l n k hkl))⟩) (modelIso hkl hln).symm
  · have he : pushout.inl (model.map (GrayMapping.pastingFace true l n k hkl))
        (model.map (GrayMapping.pastingFace false l n k hkl)) ≫ (modelIso hkl hln).hom =
          model.map (GridGlobe.row n k l hkl false) := by
      rw [modelIso_hom]
      exact rowMap_comparison hkl false
    rw [← he, Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]
  · have he : pushout.inr (model.map (GrayMapping.pastingFace true l n k hkl))
        (model.map (GrayMapping.pastingFace false l n k hkl)) ≫ (modelIso hkl hln).hom =
          model.map (GridGlobe.row n k l hkl true) := by
      rw [modelIso_hom]
      exact rowMap_comparison hkl true
    rw [← he, Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]

end
end Thomason.Construction.StrictOmegaCategory.GridGlobeCylinder

end

end OAI
