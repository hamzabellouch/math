import OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage
import OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleCurveCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AdmissibleBlowupGeometry
open CurveImageAffineCoordinates
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)
variable (C : NumericalAmpleness.IntegralCurve (blowup d))
variable (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})

abbrev imageCurve := AdmissibleCurveImage.imageCurve d C hn
abbrev sourceStructure := C.embedding ≫ structureMap d
abbrev imageStructure := (imageCurve d C hn).embedding ≫ compactificationStructureMap d
@[instance_reducible] def sourceAlgebra : Algebra ℂ C.scheme.functionField :=
  IntegralAffineOpenDimension.functionFieldAlgebra (sourceStructure d C)
@[instance_reducible] def imageAlgebra :
    Algebra ℂ (imageCurve d C hn).scheme.functionField :=
  IntegralAffineOpenDimension.functionFieldAlgebra (imageStructure d C hn)

def fieldEquiv :
    letI := imageAlgebra d C hn
    letI := sourceAlgebra d C
    (imageCurve d C hn).scheme.functionField ≃ₐ[ℂ] C.scheme.functionField :=
  fieldAlgEquiv (imageStructure d C hn) (sourceStructure d C)
    (AdmissibleCurveImage.functionFieldIso d C hn) (by
      simpa only [imageStructure, sourceStructure, structureMap, Category.assoc] using
        congrArg (fun f => f ≫ compactificationStructureMap d)
          (AdmissibleCurveImage.functionFieldIso_generic d C hn))

abbrev chart := affinePart (imageCurve d C hn).embedding (affineChart d)
abbrev chartPresentation := affinePresentation (imageCurve d C hn).embedding (affineChart d)

variable (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange)

include hm in
theorem chart_nonempty : Nonempty (chart d C hn).1 :=
  affinePart_nonempty _ _ (AdmissibleCurveImage.image_meets_chart d C hn hm)

def imageCoordinates : Fin (d.m+1) → (imageCurve d C hn).scheme.functionField :=
  letI := chart_nonempty d C hn hm
  CurveImageAffineCoordinates.coordinates (chart d C hn) (chartPresentation d C hn)

def coordinates : Fin (d.m+1) → C.scheme.functionField :=
  letI := imageAlgebra d C hn
  letI := sourceAlgebra d C
  fieldEquiv d C hn ∘ imageCoordinates d C hn hm

def y : C.scheme.functionField := coordinates d C hn hm 0

def x : Fin d.m → C.scheme.functionField := fun i => coordinates d C hn hm i.succ

@[simp] theorem full_coordinates :
    (Fin.cases (y d C hn hm) (x d C hn hm) : Fin (d.m+1) → C.scheme.functionField) =
      coordinates d C hn hm := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem field_properties :
    letI := sourceAlgebra d C
    Algebra.EssFiniteType ℂ C.scheme.functionField ∧
      Algebra.trdeg ℂ C.scheme.functionField = 1 ∧
      IntermediateField.adjoin ℂ (Set.range (coordinates d C hn hm)) = ⊤ := by
  let := sourceAlgebra d C
  let := imageAlgebra d C hn
  let := chart_nonempty d C hn hm
  obtain ⟨ht,hd,hg⟩ := CurveImageAffineCoordinates.field_properties
    (imageStructure d C hn) (imageCurve d C hn).dimension
    (chart d C hn) (chartPresentation d C hn)
    (affinePresentation_over (compactificationStructureMap d) _ _ (affineChart_over d))
  let := ht
  exact transport_field_properties (fieldEquiv d C hn)
    (imageCoordinates d C hn hm) hd hg

theorem coordinates_generic_map :
    letI := sourceAlgebra d C
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℂ) (coordinates d C hn hm)).toRingHom) ≫
      affineChart d = C.scheme.fromSpecStalk (genericPoint C.scheme) ≫
        C.embedding ≫ projection d := by
  let := sourceAlgebra d C
  let := imageAlgebra d C hn
  let := chart_nonempty d C hn hm
  have himage := CurveImageAffineCoordinates.coordinates_generic_map
    (imageStructure d C hn) (chart d C hn) (chartPresentation d C hn)
    (affinePresentation_over (compactificationStructureMap d) _ _ (affineChart_over d))
    (affineChart d) (imageCurve d C hn).embedding (affinePresentation_comp _ _)
  have he : (MvPolynomial.aeval (R := ℂ) (coordinates d C hn hm)).toRingHom =
      (AdmissibleCurveImage.functionFieldIso d C hn).hom.hom.comp
        (MvPolynomial.aeval (R := ℂ) (imageCoordinates d C hn hm)).toRingHom := by
    apply congrArg AlgHom.toRingHom
      (show MvPolynomial.aeval (R := ℂ) (coordinates d C hn hm) =
        (fieldEquiv d C hn).toAlgHom.comp
          (MvPolynomial.aeval (R := ℂ) (imageCoordinates d C hn hm)) from ?_)
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
    rfl
  rw [he, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]
  rw [show Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := ℂ) (imageCoordinates d C hn hm)).toRingHom) ≫ affineChart d =
      (imageCurve d C hn).scheme.fromSpecStalk (genericPoint (imageCurve d C hn).scheme) ≫
        (imageCurve d C hn).embedding from himage]
  exact AdmissibleCurveImage.functionFieldIso_generic d C hn

end PiExponent.AdmissibleCurveCoordinates

end

end OAI
