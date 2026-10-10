import OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization
import OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleCurveModel
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AdmissibleBlowupGeometry CurveNormalizationModel
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

structure ModelData (C : NumericalAmpleness.IntegralCurve (blowup d)) where
  E : Type
  [field : Field E]
  [algebra : Algebra ℂ E]
  [essFiniteType : Algebra.EssFiniteType ℂ E]
  coordinates : Fin (d.m+1) → E
  coordinates_generate : IntermediateField.adjoin ℂ (Set.range coordinates) = ⊤
  trdeg_one : Algebra.trdeg ℂ E = 1
  parameter : E
  parameter_transcendental : Transcendental ℂ parameter
  [parameterFinite : FiniteDimensional (IntermediateField.adjoin ℂ {parameter}) E]
  normalization : parameterCurve parameter parameter_transcendental ⟶ C.scheme
  [normalizationFinite : IsFinite normalization]
  normalization_over : normalization ≫ C.embedding ≫ structureMap d =
    parameterCurveStructureMap parameter parameter_transcendental
  chart : C.scheme.Opens
  chart_nonempty : chart ≠ ⊥
  [chartIso : IsIso (normalization ∣_ chart)]
  generic_coordinates : parameterCurveGenericPoint parameter parameter_transcendental ≫
      (normalization ≫ C.embedding ≫ projection d) =
    CurveMonomialMap.genericMonomialMap (exponents d) (constantIndex d)
      ((scale d).exponents_constant d.curveDegreeWeights_pos) (coordinateIndex d)
      ((scale d).exponents_coordinate d.curveDegreeWeights_pos) coordinates

theorem existsModelData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ t : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {t})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    Nonempty (ModelData d C) := by
  let := AdmissibleCurveCoordinates.sourceAlgebra d C
  have hp := AdmissibleCurveCoordinates.field_properties d C hn hm
  let := hp.1
  let z := AdmissibleCurveCoordinates.coordinates d C hn hm
  have hfinite := CurveParameterFinite.finite_over_every_parameter ℂ C.scheme.functionField hp.2.1
  obtain ⟨i,hi⟩ := CurveInequality.nonconstant_coordinates z hp.2.2 hp.2.1
  let f := z i
  have hf : Transcendental ℂ f := hi
  let := hfinite f hf
  obtain ⟨g,hg,hgeneric,hgfinite,W,hW,hWiso⟩ :=
    CurveNormalizationMorphism.exists_intrinsic_normalization_morphism
      (C.embedding ≫ structureMap d) C.dimension f hf
  let := hgfinite
  let := hWiso
  have hWne : W ≠ ⊥ := by
    intro he
    simp only [he, Opens.mem_bot] at hW
  have hc : parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ projection d) =
      CurveMonomialMap.genericMonomialMap (exponents d) (constantIndex d)
        ((scale d).exponents_constant d.curveDegreeWeights_pos) (coordinateIndex d)
        ((scale d).exponents_coordinate d.curveDegreeWeights_pos) z := by
    change parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ projection d) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ affineChart d
    rw [← Category.assoc, ← Category.assoc, hgeneric]
    exact (AdmissibleCurveCoordinates.coordinates_generic_map d C hn hm).symm
  exact ⟨{ E := C.scheme.functionField
           field := inferInstance
           algebra := inferInstance
           essFiniteType := hp.1
           coordinates := z
           coordinates_generate := hp.2.2
           trdeg_one := hp.2.1
           parameter := f
           parameter_transcendental := hf
           parameterFinite := inferInstance
           normalization := g
           normalizationFinite := hgfinite
           normalization_over := hg
           chart := W
           chart_nonempty := hWne
           chartIso := hWiso
           generic_coordinates := hc }⟩

end PiExponent.AdmissibleCurveModel

end

end OAI
