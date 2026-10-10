import OAI.Algebra.Finitistic.Localization.CompletedImageEvaluation

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
universe u v w z
section General
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type w} [Category.{z} D] [Preadditive D] [IsIdempotentComplete D]
variable (F : C ⥤ D) [F.Additive] (U : Karoubi C) (I : D)
variable (π : F.obj U.X ⟶ I) (ι : I ⟶ F.obj U.X)
variable (hπι : π ≫ ι = F.map U.p) (hιπ : ι ≫ π = 𝟙 I)

omit [Preadditive C] [Preadditive D] [F.Additive] in
theorem completedExtensionImageSquare (a : U ⟶ U) (b : I ⟶ I)
    (h : F.map a.f ≫ π = π ≫ b) :
    ((functorExtension C D).obj F).map a ≫
      (completedExtensionImageIso F U I π ι hπι hιπ).hom =
    (completedExtensionImageIso F U I π ι hπι hιπ).hom ≫ b := by
  let e := splitKaroubiIso (F.map U.p) (by rw [← F.map_comp, U.idem]) π ι hπι hιπ
  have he : ((functorExtension₂ C D).obj F).map a ≫ e.hom =
      e.hom ≫ (toKaroubi D).map b := by
    apply Karoubi.Hom.ext
    exact h
  change (toKaroubiEquivalence D).inverse.map (((functorExtension₂ C D).obj F).map a) ≫
    ((toKaroubiEquivalence D).inverse.map e.hom ≫ (toKaroubiEquivalence D).unitIso.inv.app I) =
    ((toKaroubiEquivalence D).inverse.map e.hom ≫ (toKaroubiEquivalence D).unitIso.inv.app I) ≫ b
  erw [← Category.assoc, ← Functor.map_comp, he, Functor.map_comp, Category.assoc]
  erw [(toKaroubiEquivalence D).unitIso.inv.naturality b]
  exact (Category.assoc _ _ _).symm
end General

section Image
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable (p a : Module.End k V) (hp : p*p=p)

def imageCornerEnd : ModuleCat.of k (LinearMap.range p) ⟶ ModuleCat.of k (LinearMap.range p) :=
  imageInclusion p ≫ ModuleCat.ofHom a ≫ imageProjection p

include hp in
lemma image_corner_square :
    ModuleCat.ofHom (p*a*p) ≫ imageProjection p = imageProjection p ≫ imageCornerEnd p a := by
  change ((ModuleCat.ofHom p ≫ ModuleCat.ofHom a) ≫ ModuleCat.ofHom p) ≫ imageProjection p = _
  rw [← image_projection_inclusion p]
  simp only [imageCornerEnd, Category.assoc, image_inclusion_projection p hp, Category.comp_id]

include hp in
/-- When a commutes with p, the corner operator is the restriction of a to the image. -/
lemma imageCornerEnd_apply (ha : p*a=a*p) (x : LinearMap.range p) :
    ((imageCornerEnd p a) x).val = a x.val := by
  change p (a x.val) = a x.val
  have h := LinearMap.congr_fun ha x.val
  change p (a x.val) = a (p x.val) at h
  rw [h]
  obtain ⟨y,hy⟩ := x.property
  have hp' : p x.val = x.val := by rw [← hy]; exact LinearMap.congr_fun hp y
  rw [hp']
end Image

variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
variable (X : Representation P Y) (e a : PresentedAlgebra P) (he : e*e=e)

def quotientCornerEnd : quotientSummand e he ⟶ quotientSummand e he :=
  ⟨quotientAction P (e*a*e), by
    change (quotientAction P e * quotientAction P (e*a*e)) * quotientAction P e = _
    simp only [← map_mul]
    congr 1
    simp only [← mul_assoc, he]
    rw [mul_assoc (e*a) e e, he]⟩

def evaluatedCornerEnd : evaluatedImageDerived X e ⟶ evaluatedImageDerived X e :=
  (derivedTargetInclusion (k := k)).preimage (DerivedCategory.Qh.map
    ((vectorStalk (k := k)).map (imageCornerEnd
      (liftedEndHom (givenAction X e)).hom (liftedEndHom (givenAction X a)).hom)))

include he in
lemma derived_corner_projection_square :
    (derivedQuotientEvaluation X ⋙ derivedTargetInclusion (k := k)).map
      (quotientAction P (e*a*e)) ≫ derivedImageProjection X e =
    derivedImageProjection X e ≫ (derivedTargetInclusion (k := k)).map (evaluatedCornerEnd X e a) := by
  unfold evaluatedCornerEnd
  erw [Functor.map_preimage]
  unfold derivedImageProjection
  erw [← Category.assoc, derived_quotientAction_square, Category.assoc]
  erw [← Functor.map_comp, ← Functor.map_comp]
  have h := image_corner_square (liftedEndHom (givenAction X e)).hom
    (liftedEndHom (givenAction X a)).hom (lifted_action_idempotent X e he)
  have hc : liftedEndHom (givenAction X (e*a*e)) = ModuleCat.ofHom
      ((liftedEndHom (givenAction X e)).hom * (liftedEndHom (givenAction X a)).hom *
        (liftedEndHom (givenAction X e)).hom) := by
    simp only [map_mul]
    rfl
  erw [hc, h, Functor.map_comp, Functor.map_comp, ← Category.assoc]
  rfl

/-- The complete derived evaluation intertwines every corner endomorphism with
its concrete action on eY; this includes e alpha(r) e from Section 3. -/
theorem completed_corner_square :
    (completedDerivedEvaluation X).map (quotientCornerEnd e a he) ≫
      (completedSummandImageIso X e he).hom =
    (completedSummandImageIso X e he).hom ≫ evaluatedCornerEnd X e a := by
  apply completedExtensionImageSquare
  apply (derivedTargetInclusion (k := k)).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  erw [Functor.map_preimage]
  exact derived_corner_projection_square X e a he

omit [FiniteDimensional k Y] in
include he in
/-- For a central e and any algebra endomorphism alpha, the concrete map on eY
is the restriction of alpha(r), exactly as in the manuscript. -/
theorem central_alpha_restriction (hec : ∀ b : PresentedAlgebra P, e*b=b*e)
    (α : PresentedAlgebra P →ₐ[k] PresentedAlgebra P) (b : PresentedAlgebra P)
    (y : evaluatedImage X e) :
    ((imageCornerEnd (liftedEndHom (givenAction X e)).hom
      (liftedEndHom (givenAction X (α b))).hom) y).val =
      (liftedEndHom (givenAction X (α b))).hom y.val := by
  apply imageCornerEnd_apply _ _ (lifted_action_idempotent X e he)
  have h := congrArg (fun c => (liftedEndHom (givenAction X c)).hom) (hec (α b))
  simp only [map_mul] at h
  exact h
end LittleFinitistic.QuadraticEncoding

end

end OAI
