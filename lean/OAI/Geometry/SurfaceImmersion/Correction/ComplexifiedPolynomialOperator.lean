import OAI.Geometry.SurfaceImmersion.Correction.SupportedPolynomialOperator
import OAI.Geometry.SurfaceImmersion.Geometry.ComplexFirstVariation

namespace OAI

/-! Complexification of the actual supported polynomial linearization. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

def realFieldCLM : (Fin 4 → ℂ) →L[ℝ] Space :=
  ContinuousLinearMap.pi fun a => Complex.reCLM.comp (ContinuousLinearMap.proj a)

def imagFieldCLM : (Fin 4 → ℂ) →L[ℝ] Space :=
  ContinuousLinearMap.pi fun a => Complex.imCLM.comp (ContinuousLinearMap.proj a)

namespace Expression

def complexVariationLM {O : Set LowJet} {U : Set Base} {G : Base → Space} {e : Expression}
    (hO : IsOpen O) (hU : IsOpen U) (he : e.SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (t : ℝ) :
    SupportedField (F := Fin 4 → ℂ) K →ₗ[ℝ] SupportedField (F := ℂ) K :=
  let R := variationLM hO hU he hG hQ K hKU t
  (ContDiffMapSupportedIn.postcompLM Complex.ofRealCLM).comp
      (R.comp (ContDiffMapSupportedIn.postcompLM realFieldCLM)) +
    (ContDiffMapSupportedIn.postcompLM (Complex.I • Complex.ofRealCLM)).comp
      (R.comp (ContDiffMapSupportedIn.postcompLM imagFieldCLM))

/-- The bundled operator is the same complex first variation whose
conjugated finite-jet estimates were proved above. -/
lemma complexVariationLM_apply {O : Set LowJet} {U : Set Base} {G : Base → Space} {e : Expression}
    (hO : IsOpen O) (hU : IsOpen U) (he : e.SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (t : ℝ)
    (H : SupportedField (F := Fin 4 → ℂ) K) (p : Base) :
    complexVariationLM hO hU he hG hQ K hKU t H p =
      ((ofExpression e).differentiate 0).evalComplex G (complexDirectionData G H) (p, t) := by
  change (e.variation G (realField H) (p, t) : ℂ) +
    Complex.I * (e.variation G (imagField H) (p, t) : ℂ) = _
  exact (complex_first_variation e G H.contDiff (p, t)).symm

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
