import OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite
import OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel
import OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing
import OAI.NumberTheory.PiExponent.Jets.DVRBranch
import OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField

namespace OAI

noncomputable section
namespace PiExponent.PlaceLocalRing
open CurveZeroPole CurveValuationCenter PlaceParameterModel

theorem residue_integral_of_algEquiv
    {F A B : Type*} [Field F] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] [IsLocalRing A] [IsLocalRing B]
    [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] (e : A ≃ₐ[F] B) :
    Algebra.IsIntegral F (IsLocalRing.ResidueField B) := by
  constructor
  intro x
  obtain ⟨y,rfl⟩ := (IsLocalRing.ResidueField.mapAlgEquiv e).surjective x
  exact (Algebra.IsIntegral.isIntegral y).map (IsLocalRing.ResidueField.mapAlgEquiv e).toAlgHom

theorem residue_integral
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (htrdeg : Algebra.trdeg ℂ E ≤ 1) (p : NormalizedPlace ℂ E) :
    Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)) := by
  let f := parameter p
  have hf : Transcendental ℂ f := parameter_transcendental p
  let := CurveParameterFinite.finiteDimensional_adjoin_singleton ℂ E htrdeg hf
  let := ParameterResidueField.parameterChartConstants f hf
  let q := parameterCenterPlace f hf p.valuation p.constants_nonneg (parameter_positive p)
  let := ParameterResidueField.parameter_residue_integral f hf q
  exact residue_integral_of_algEquiv (A := Localization.AtPrime q.1)
    (parameterCenterLocalAlgEquiv f hf p (parameter_positive p))

def expansion
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (htrdeg : Algebra.trdeg ℂ E ≤ 1) (p : NormalizedPlace ℂ E) :
    PlaceValuationRing.ring p →ₐ[ℂ] PowerSeries ℂ :=
  letI := residue_integral htrdeg p
  DVRBranch.expansion ℂ (PlaceValuationRing.ring p)

theorem expansion_injective
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (htrdeg : Algebra.trdeg ℂ E ≤ 1) (p : NormalizedPlace ℂ E) :
    Function.Injective (expansion htrdeg p) := by
  let := residue_integral htrdeg p
  exact DVRBranch.expansion_injective ℂ (PlaceValuationRing.ring p)

theorem expansion_order
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (htrdeg : Algebra.trdeg ℂ E ≤ 1) (p : NormalizedPlace ℂ E)
    (a : PlaceValuationRing.ring p) :
    PowerSeries.order (expansion htrdeg p a) =
      IsDiscreteValuationRing.addVal (PlaceValuationRing.ring p) a := by
  let := residue_integral htrdeg p
  exact DVRBranch.expansion_order ℂ (PlaceValuationRing.ring p) a

end PiExponent.PlaceLocalRing

end

end OAI
