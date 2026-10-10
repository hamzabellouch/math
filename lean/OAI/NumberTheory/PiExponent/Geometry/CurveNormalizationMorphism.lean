import OAI.NumberTheory.PiExponent.Geometry.BirationalOpenIso
import OAI.NumberTheory.PiExponent.Geometry.CurveGeometricFunctionField
import OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomial
import OAI.NumberTheory.PiExponent.Geometry.CurveMorphismFinite
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveNormalizationMorphism
open AlgebraicGeometry CategoryTheory
open CurveNormalizationModel

@[instance_reducible] def structureFieldAlgebra
    {F : Type u} [Field F] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) : Algebra F X.functionField :=
  (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra

theorem genericPoint_over_structure
    {F : Type u} [Field F] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) :
    letI := structureFieldAlgebra p
    X.fromSpecStalk (genericPoint X) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap F X.functionField)) := by
  let := structureFieldAlgebra p
  exact (Spec.map_preimage _).symm

theorem genericPoint_over_section_coefficients
    {F : Type u} [Field F] {X : Scheme.{u}} [IsIntegral X]
    [Algebra F Γ(X, ⊤)] :
    letI := CurveGeometricFunctionField.intrinsicFunctionFieldAlgebra F X
    X.fromSpecStalk (genericPoint X) ≫
      (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, ⊤)))) =
        Spec.map (CommRingCat.ofHom (algebraMap F X.functionField)) := by
  let := CurveGeometricFunctionField.intrinsicFunctionFieldAlgebra F X
  rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rfl

theorem isDominant_of_generic_identity
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) (e : Y.functionField ≃+* X.functionField)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y) ≫ g = X.fromSpecStalk (genericPoint X)) :
    IsDominant g := by
  have : IsDominant ((Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y)) ≫ g) := by
    rw [Category.assoc, he]
    exact CurveStalkGluing.isDominant_fromSpecFunctionField
  exact IsDominant.of_comp (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Y.fromSpecStalk (genericPoint Y)) g

theorem nontrivial_of_dimension_one (X : Scheme.{u})
    (hdim : topologicalKrullDim X = 1) : Nontrivial X := by
  classical
  by_contra h
  have : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
  have hzero := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at hzero
  norm_num at hzero

theorem exists_model_morphism
    {F : Type u} [Field F] [CharZero F]
    {X : Scheme.{u}} [IsIntegral X] [Algebra F X.functionField]
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (hp : X.fromSpecStalk (genericPoint X) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap F X.functionField)))
    (f : X.functionField) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) X.functionField] :
    ∃ g : parameterCurve f hf ⟶ X,
      g ≫ p = parameterCurveStructureMap f hf ∧
      parameterCurveGenericPoint f hf ≫ g = X.fromSpecStalk (genericPoint X) ∧
      IsProper g ∧ IsDominant g := by
  obtain ⟨g, hover, hgeneric⟩ := CurveGlobalMonomial.exists_parameterCurve_extension
    f hf p (X.fromSpecStalk (genericPoint X)) hp
  have : IsProper (g ≫ p) := by
    rw [hover]
    infer_instance
  have : IsProper g := IsProper.of_comp g p
  have : IsDominant g := isDominant_of_generic_identity g
    (parameterCurveFunctionFieldEquiv f hf) (by
      simpa only [parameterCurveGenericPoint, Category.assoc] using hgeneric)
  exact ⟨g, hover, hgeneric, inferInstance, inferInstance⟩

theorem exists_intrinsic_model_morphism
    {F : Type u} [Field F] [CharZero F]
    {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p] :
    letI := structureFieldAlgebra p
    ∀ (f : X.functionField) (hf : Transcendental F f),
      ∀ [FiniteDimensional (IntermediateField.adjoin F {f}) X.functionField],
      ∃ g : parameterCurve f hf ⟶ X,
        g ≫ p = parameterCurveStructureMap f hf ∧
        parameterCurveGenericPoint f hf ≫ g = X.fromSpecStalk (genericPoint X) ∧
        IsProper g ∧ IsDominant g := by
  let := structureFieldAlgebra p
  intro f hf hfinite
  exact exists_model_morphism p (genericPoint_over_structure p) f hf

theorem exists_finite_model_morphism
    {F : Type u} [Field F] [CharZero F]
    {X : Scheme.{u}} [IsIntegral X] [Nontrivial X] [Algebra F X.functionField]
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (hp : X.fromSpecStalk (genericPoint X) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap F X.functionField)))
    (f : X.functionField) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) X.functionField] :
    ∃ g : parameterCurve f hf ⟶ X,
      g ≫ p = parameterCurveStructureMap f hf ∧
      parameterCurveGenericPoint f hf ≫ g = X.fromSpecStalk (genericPoint X) ∧
      IsFinite g ∧ ∃ U : X.Opens, genericPoint X ∈ U ∧ IsIso (g ∣_ U) := by
  obtain ⟨g, hover, hgeneric, hproper, hdominant⟩ := exists_model_morphism p hp f hf
  have : IsProper g := hproper
  have : IsDominant g := hdominant
  have hfinite : IsFinite g := CurveMorphismFinite.isFinite_of_proper_dominant g
    (parameterCurve_dimension_le_one f hf)
  obtain ⟨U, hU, hUiso⟩ := BirationalOpenIso.exists_open_iso_of_generic_inverse g
    (parameterCurveFunctionFieldEquiv f hf) (by
      simpa only [parameterCurveGenericPoint, Category.assoc] using hgeneric)
  exact ⟨g, hover, hgeneric, hfinite, U, hU, hUiso⟩

theorem exists_intrinsic_normalization_morphism
    {F : Type u} [Field F] [CharZero F]
    {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (hdim : topologicalKrullDim X = 1) :
    letI := structureFieldAlgebra p
    ∀ (f : X.functionField) (hf : Transcendental F f),
      ∀ [FiniteDimensional (IntermediateField.adjoin F {f}) X.functionField],
      ∃ g : parameterCurve f hf ⟶ X,
        g ≫ p = parameterCurveStructureMap f hf ∧
        parameterCurveGenericPoint f hf ≫ g = X.fromSpecStalk (genericPoint X) ∧
        IsFinite g ∧ ∃ U : X.Opens, genericPoint X ∈ U ∧ IsIso (g ∣_ U) := by
  let := structureFieldAlgebra p
  intro f hf hfinite
  have : Nontrivial X := nontrivial_of_dimension_one X hdim
  exact exists_finite_model_morphism p (genericPoint_over_structure p) f hf

end PiExponent.CurveNormalizationMorphism

end

end OAI
