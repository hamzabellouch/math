import OAI.NumberTheory.PiExponent.Geometry.CurveModelFieldEmbedding
import OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [FiniteDimensional (IntermediateField.adjoin F {f}) E]


theorem parameterCurveGenericPoint_eq_infinityChart :
    parameterCurveGenericPoint f hf =
      Spec.map (CommRingCat.ofHom
        (algebraMap (parameterChart f⁻¹ (transcendental_inverse f hf)) E)) ≫
        infinityChartInclusion f hf := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let := parameterChartFractionRing f⁻¹ (transcendental_inverse f hf)
  unfold parameterCurveGenericPoint
  rw [parameterCurveFunctionFieldEquiv_eq_infinity]
  change Spec.map (functionFieldRestriction (infinityChartInclusion f hf) ≫
      CommRingCat.ofHom
        (affineFunctionFieldEquiv (parameterChart f⁻¹ (transcendental_inverse f hf)) E).toRingHom) ≫
      (parameterCurve f hf).fromSpecStalk (genericPoint (parameterCurve f hf)) = _
  let i := infinityChartInclusion f hf
  let e := Spec.map (CommRingCat.ofHom
    (affineFunctionFieldEquiv (parameterChart f⁻¹ (transcendental_inverse f hf)) E).toRingHom)
  let r := Spec.map (functionFieldRestriction i)
  let q := (parameterCurve f hf).fromSpecStalk (genericPoint (parameterCurve f hf))
  have hmap := congrArg (fun k => k ≫ q)
    (Spec.map_comp (functionFieldRestriction i) (CommRingCat.ofHom
      (affineFunctionFieldEquiv (parameterChart f⁻¹ (transcendental_inverse f hf)) E).toRingHom))
  have hrestrict := congrArg (fun k => e ≫ k) (functionFieldRestriction_fromSpecStalk i)
  have haffine := congrArg (fun k => k ≫ i)
    (affineFunctionFieldEquiv_fromSpecStalk (parameterChart f⁻¹ (transcendental_inverse f hf)) E)
  have hassoc := Category.assoc e
    ((Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))).fromSpecStalk
      (genericPoint (Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))))) i
  exact hmap.trans ((Category.assoc e r q).trans
    (hrestrict.trans (hassoc.symm.trans haffine)))

end PiExponent.CurveNormalizationModel

end

end OAI
