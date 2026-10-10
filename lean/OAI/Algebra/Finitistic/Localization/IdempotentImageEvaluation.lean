import OAI.Algebra.Finitistic.Localization.KaroubiEvaluation
import OAI.Algebra.Finitistic.Localization.DerivedActionCompatibility

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
universe u v w z
section Image
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable (p : Module.End k V) (hp : p*p=p)

def imageProjection : ModuleCat.of k V ⟶ ModuleCat.of k (LinearMap.range p) :=
  ModuleCat.ofHom p.rangeRestrict

def imageInclusion : ModuleCat.of k (LinearMap.range p) ⟶ ModuleCat.of k V :=
  ModuleCat.ofHom (LinearMap.range p).subtype

lemma image_projection_inclusion : imageProjection p ≫ imageInclusion p = ModuleCat.ofHom p := rfl
include hp in
lemma image_inclusion_projection : imageInclusion p ≫ imageProjection p = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y,hy⟩ := x.property
  change p x.val = x.val
  rw [← hy]
  exact LinearMap.congr_fun hp y

variable {D : Type w} [Category.{z} D] (F : ModuleCat.{v} k ⥤ D)

/-- A functor takes a concrete linear idempotent's formal image to the actual image module. -/
def linearImageKaroubiIso :
    (⟨F.obj (ModuleCat.of k V), F.map (ModuleCat.ofHom p), by
      rw [← F.map_comp]
      congr 1
      exact congrArg ModuleCat.ofHom hp⟩ : Karoubi D) ≅
    (toKaroubi D).obj (F.obj (ModuleCat.of k (LinearMap.range p))) :=
  splitKaroubiIso _ _ (F.map (imageProjection p)) (F.map (imageInclusion p))
    (by rw [← F.map_comp, image_projection_inclusion])
    (by rw [← F.map_comp, image_inclusion_projection p hp, F.map_id])
end Image

variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)
variable (r : PresentedAlgebra P) (hr : r*r=r)

/-- The actual image eY, represented in the same universe as tensor evaluation. -/
def evaluatedImage := LinearMap.range ((liftedEndHom (givenAction X r)).hom)

include hr in
lemma lifted_action_idempotent :
    (liftedEndHom (givenAction X r)).hom * (liftedEndHom (givenAction X r)).hom =
      (liftedEndHom (givenAction X r)).hom := by
  have h := congrArg (fun a => (liftedEndHom (givenAction X a)).hom) hr
  simp only [map_mul] at h
  exact h

/-- The formal evaluated summand is the stalk of the concrete image of the action. -/
def stalkSummandImageIso : stalkSummand X r hr ≅
    (toKaroubi _).obj ((vectorStalk (k := k)).obj (ModuleCat.of k (evaluatedImage X r))) := by
  let e := linearImageKaroubiIso ((liftedEndHom (givenAction X r)).hom)
    (lifted_action_idempotent X r hr) (vectorStalk (k := k))
  dsimp [stalkSummand, givenStalkAction, identifiedEndHom, evaluatedImage] at e ⊢
  exact e

/-- Section 3: evaluation sends the formal quotient summand U to eY. -/
def quotientSummandImageIso : (karoubiEvaluation X).obj (quotientSummand r hr) ≅
    (toKaroubi _).obj ((vectorStalk (k := k)).obj (ModuleCat.of k (evaluatedImage X r))) :=
  evaluatedSummandIso X r hr ≪≫ stalkSummandImageIso X r hr

instance evaluatedImageFinite [FiniteDimensional k Y] : FiniteDimensional k (evaluatedImage X r) := by
  have : FiniteDimensional k (ULift.{u} Y) :=
    Module.Finite.of_injective (ULift.moduleEquiv : ULift.{u} Y ≃ₗ[k] Y).toLinearMap
      ULift.moduleEquiv.injective
  let p : Module.End k (ULift.{u} Y) := (liftedEndHom (givenAction X r)).hom
  have hp : FiniteDimensional k p.range := inferInstance
  exact hp
end LittleFinitistic.QuadraticEncoding

end

end OAI
