import OAI.Algebra.Finitistic.Localization.CompletedDerivedEvaluation

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy
universe u v
private theorem sandwich_cancel {C : Type*} [Category C] {A B I : C}
    (e : A ≅ B) (p : B ⟶ I) (i : I ⟶ B) :
    ((e.hom ≫ p) ≫ (i ≫ e.inv)) ≫ e.hom = e.hom ≫ (p ≫ i) := by
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]

variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
variable (X : Representation P Y) (r : PresentedAlgebra P) (hr : r*r=r)

/-- The image vector space, as an actual bounded finite-dimensional stalk complex. -/
def evaluatedImageK : K.{u,max u v} k :=
  ⟨(vectorStalk (k := k)).obj (ModuleCat.of k (evaluatedImage X r)),
    single_property (ModuleCat.of k (evaluatedImage X r)) 0⟩

def evaluatedImageDerived : FiniteVectorDerived.{u,v} (k := k) :=
  (derivedEmbedding k).toEssImage.obj (evaluatedImageK X r)

abbrev derivedTargetInclusion := (derivedEmbedding.{u,max u v} k).essImage.ι

def derivedImageProjection :
    (derivedTargetInclusion (k := k)).obj ((derivedQuotientEvaluation X).obj (vertexQ P 0)) ⟶
    (derivedTargetInclusion (k := k)).obj (evaluatedImageDerived X r) :=
  (derivedVertexIso X 0).hom ≫ DerivedCategory.Qh.map
    ((vectorStalk (k := k)).map (imageProjection (liftedEndHom (givenAction X r)).hom))

def derivedImageInclusion :
    (derivedTargetInclusion (k := k)).obj (evaluatedImageDerived X r) ⟶
    (derivedTargetInclusion (k := k)).obj ((derivedQuotientEvaluation X).obj (vertexQ P 0)) :=
  DerivedCategory.Qh.map
    ((vectorStalk (k := k)).map (imageInclusion (liftedEndHom (givenAction X r)).hom)) ≫
      (derivedVertexIso X 0).inv

include hr in
lemma derived_image_inclusion_projection :
    derivedImageInclusion X r ≫ derivedImageProjection X r = 𝟙 _ := by
  dsimp [derivedImageInclusion, derivedImageProjection]
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  erw [← Functor.map_comp, ← Functor.map_comp,
    image_inclusion_projection _ (lifted_action_idempotent X r hr)]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

lemma derived_image_projection_inclusion :
    derivedImageProjection X r ≫ derivedImageInclusion X r =
      (derivedQuotientEvaluation X ⋙ derivedTargetInclusion (k := k)).map (quotientAction P r) := by
  apply (cancel_mono (derivedVertexIso X 0).hom).mp
  dsimp [derivedImageProjection, derivedImageInclusion]
  erw [sandwich_cancel (derivedVertexIso X 0)
    (DerivedCategory.Qh.map ((vectorStalk (k := k)).map
      (imageProjection (liftedEndHom (givenAction X r)).hom)))
    (DerivedCategory.Qh.map ((vectorStalk (k := k)).map
      (imageInclusion (liftedEndHom (givenAction X r)).hom)))]
  erw [← Functor.map_comp, ← Functor.map_comp, image_projection_inclusion]
  exact (derived_quotientAction_square X r).symm

/-- The full completed derived evaluation takes U to the actual finite-dimensional eY stalk. -/
def completedSummandImageIso :
    (completedDerivedEvaluation X).obj (quotientSummand r hr) ≅ evaluatedImageDerived X r :=
  completedExtensionImageIso (derivedQuotientEvaluation X) (quotientSummand r hr)
    (evaluatedImageDerived X r)
    ((derivedTargetInclusion (k := k)).preimage (derivedImageProjection X r))
    ((derivedTargetInclusion (k := k)).preimage (derivedImageInclusion X r))
    (by
      apply (derivedTargetInclusion (k := k)).map_injective
      rw [Functor.map_comp]
      erw [Functor.map_preimage, Functor.map_preimage]
      exact derived_image_projection_inclusion X r)
    (by
      apply (derivedTargetInclusion (k := k)).map_injective
      erw [Functor.map_comp, CategoryTheory.Functor.map_id]
      erw [Functor.map_preimage, Functor.map_preimage]
      exact derived_image_inclusion_projection X r hr)
end LittleFinitistic.QuadraticEncoding

end

end OAI
