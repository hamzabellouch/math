import OAI.Algebra.Finitistic.Localization.SourceActionEvaluation
import OAI.Algebra.Finitistic.Localization.FormalSummandAction

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceImageEvaluation
private theorem sandwich_map_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A : D} {B I : C} (e : A ≅ F.obj B)
    (p : B ⟶ I) (i : I ⟶ B) (b : B ⟶ B) (a : A ⟶ A)
    (h : p ≫ i = b) (sq : a ≫ e.hom = e.hom ≫ F.map b) :
    (e.hom ≫ F.map p) ≫ (F.map i ≫ e.inv) = a := by
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [← F.map_comp, h, sq]

open QuadraticEncoding FiniteProjectiveHomotopy
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R)
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

abbrev representation := SourceActionEvaluation.representation (Y := Y) E
abbrev evaluation := SourceEvaluation.derived (representation (Y := Y) E)
abbrev action (r : R) : End (ModuleCat.of k (ULift.{u} Y)) :=
  liftedEndHom ((Algebra.lsmul k k Y) r)
abbrev vertexIso := SourceEvaluation.derivedVertexIso (representation (Y := Y) E) 0

def completed : Karoubi (SourceVerdier.Q E.relations) ⥤ FiniteVectorDerived.{u,v} (k := k) :=
  (functorExtension _ _).obj (evaluation (Y := Y) E)
instance : (completed (Y := Y) E).Additive := completedExtensionAdditive _
def factors : toKaroubi (SourceVerdier.Q E.relations) ⋙ completed (Y := Y) E ≅ evaluation (Y := Y) E :=
  completedExtensionFactors _

/-- Literal range of the selecting operator on the canonical universe lift of Y. -/
abbrev imageSpace (e : R) := LinearMap.range (action (k := k) (Y := Y) e).hom

def imageK (e : R) : K.{u,max u v} k :=
  ⟨(vectorStalk (k := k)).obj (ModuleCat.of k (imageSpace (k := k) (Y := Y) e)),
    single_property _ 0⟩
def imageDerived (e : R) : FiniteVectorDerived.{u,v} (k := k) :=
  (derivedEmbedding k).toEssImage.obj (imageK (k := k) (Y := Y) e)

omit [FiniteDimensional k Y] in
lemma action_idem (e : R) (he : e*e=e) :
    (action (k := k) (Y := Y) e).hom * (action (k := k) (Y := Y) e).hom = (action (k := k) (Y := Y) e).hom := by
  have h := congrArg (fun r => (action (k := k) (Y := Y) r).hom) he
  simp only [action,map_mul] at h
  exact h

abbrev U (e : R) (he : e*e=e) := FormalSummandAction.summand (SourceQuotientAction.theta E) e he

def projection (e : R) :
    (derivedTargetInclusion (k := k)).obj ((evaluation (Y := Y) E).obj (SourceQuotientAction.vertex E.relations 0)) ⟶
      (derivedTargetInclusion (k := k)).obj (imageDerived (k := k) (Y := Y) e) :=
  (vertexIso (Y := Y) E).hom ≫ DerivedCategory.Qh.map
    ((vectorStalk (k := k)).map (imageProjection (action (k := k) (Y := Y) e).hom))
def inclusion (e : R) :
    (derivedTargetInclusion (k := k)).obj (imageDerived (k := k) (Y := Y) e) ⟶
      (derivedTargetInclusion (k := k)).obj ((evaluation (Y := Y) E).obj (SourceQuotientAction.vertex E.relations 0)) :=
  DerivedCategory.Qh.map ((vectorStalk (k := k)).map (imageInclusion (action (k := k) (Y := Y) e).hom)) ≫
    (vertexIso (Y := Y) E).inv

lemma inclusion_projection (e : R) (he : e*e=e) :
    inclusion (Y := Y) E e ≫ projection (Y := Y) E e = 𝟙 _ := by
  dsimp only [inclusion,projection]
  erw [Category.assoc,Iso.inv_hom_id_assoc]
  erw [← Functor.map_comp,← Functor.map_comp,image_inclusion_projection _ (action_idem (k := k) (Y := Y) e he)]
  erw [CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_id]
  rfl
lemma projection_inclusion (e : R) :
    projection (Y := Y) E e ≫ inclusion (Y := Y) E e =
      (evaluation (Y := Y) E ⋙ derivedTargetInclusion (k := k)).map (SourceQuotientAction.theta E e) := by
  exact sandwich_map_eq ((vectorStalk (k := k)) ⋙ DerivedCategory.Qh)
    (vertexIso (Y := Y) E) (imageProjection (action (k := k) (Y := Y) e).hom)
    (imageInclusion (action (k := k) (Y := Y) e).hom) (action (k := k) (Y := Y) e)
    ((evaluation (Y := Y) E ⋙ derivedTargetInclusion (k := k)).map (SourceQuotientAction.theta E e))
    (image_projection_inclusion _) (SourceActionEvaluation.derived_action_square (Y := Y) E e)

def summandImageIso (e : R) (he : e*e=e) :
    (completed (Y := Y) E).obj (U E e he) ≅ imageDerived (k := k) (Y := Y) e :=
  completedExtensionImageIso (evaluation (Y := Y) E) (U E e he) (imageDerived (k := k) (Y := Y) e)
    ((derivedTargetInclusion (k := k)).preimage (projection (Y := Y) E e))
    ((derivedTargetInclusion (k := k)).preimage (inclusion (Y := Y) E e))
    (by
      apply (derivedTargetInclusion (k := k)).map_injective
      rw [Functor.map_comp]
      erw [Functor.map_preimage,Functor.map_preimage]
      exact projection_inclusion E e)
    (by
      apply (derivedTargetInclusion (k := k)).map_injective
      erw [Functor.map_comp,CategoryTheory.Functor.map_id]
      erw [Functor.map_preimage,Functor.map_preimage]
      exact inclusion_projection E e he)
end LittleFinitistic.SourceImageEvaluation

end

end OAI
