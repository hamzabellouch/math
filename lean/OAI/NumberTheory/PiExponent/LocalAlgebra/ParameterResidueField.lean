import OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter

namespace OAI

noncomputable section
namespace PiExponent.ParameterResidueField
open scoped Polynomial nonZeroDivisors
open CurveZeroPole CurveValuationCenter

theorem residue_finite {F S : Type*} [Field F] [CommRing S] [Algebra F S]
    [Algebra.FiniteType F S] (q : Ideal S) [q.IsMaximal] : Module.Finite F q.ResidueField := by
  let : Algebra.FiniteType F q.ResidueField :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom F S q.ResidueField)
      (Ideal.algebraMap_residueField_surjective q)
  exact finite_of_finite_type_of_isJacobsonRing F q.ResidueField

abbrev parameterChartConstants
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Algebra F (parameterChart f hf) :=
  let := parameterPolynomialAlgebra f hf
  ((algebraMap F[X] (parameterChart f hf)).comp Polynomial.C).toAlgebra

theorem parameterChartConstants_tower
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    letI := parameterPolynomialAlgebra f hf
    letI := parameterChartConstants f hf
    IsScalarTower F F[X] (parameterChart f hf) := by
  let := parameterPolynomialAlgebra f hf
  let := parameterChartConstants f hf
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem parameter_residue_finite
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) :
    letI := parameterChartConstants f hf
    Module.Finite F (IsLocalRing.ResidueField (Localization.AtPrime q.1)) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let := parameterChartConstants f hf
  let := parameterChartConstants_tower f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  let : Algebra.FiniteType F S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F F[X]) (inferInstance : Algebra.FiniteType F[X] S)
  let : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q.1 (zeroPrime F)
  exact residue_finite q.1

theorem parameter_residue_integral
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) :
    letI := parameterChartConstants f hf
    Algebra.IsIntegral F (IsLocalRing.ResidueField (Localization.AtPrime q.1)) := by
  let := parameterChartConstants f hf
  let := parameter_residue_finite f hf q
  exact Algebra.IsIntegral.of_finite F _

end PiExponent.ParameterResidueField

end

end OAI
