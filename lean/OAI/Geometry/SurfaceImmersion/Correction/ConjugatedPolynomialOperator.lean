import OAI.Geometry.SurfaceImmersion.Correction.ComplexifiedPolynomialOperator
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedPhaseOperators
import OAI.Geometry.SurfaceImmersion.Geometry.ConjugatedMultilinearBounds

namespace OAI

/-! The oscillatory estimates apply to the actual conjugated polynomial
linearization on supported smooth fields. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma iteratedDirectional_zero {A F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (w : List A) :
    iteratedDirectional w (fun _ : A => (0 : F)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons v w ih => simp [iteratedDirectional, ih]

def singlePhase (φ : Base → ℝ) : Fin 3 → Base → ℝ := ![φ, 0, 0]
def singleDirection (H : Base → Fin 4 → ℂ) : DirectionFields := ![H, 0, 0]

lemma singlePhase_smooth {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∀ i, ContDiff ℝ ∞ (singlePhase φ i) := by
  intro i
  fin_cases i
  · exact hφ
  · exact contDiff_const
  · exact contDiff_const

lemma singleDirection_smooth {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) :
    ∀ i, ContDiff ℝ ∞ (singleDirection H i) := by
  intro i
  fin_cases i
  · exact hH
  · exact contDiff_const
  · exact contDiff_const

lemma single_oscillatoryData (G : Base → Space) (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) (τ : ℝ) :
    oscillatoryData G (singlePhase φ) (singleDirection H) τ =
      complexDirectionData G (fun p => phase τ φ p • H p) := by
  funext i w a p
  fin_cases i
  · rfl
  · rfl
  · change iteratedDirectional (w.map coordinateVector)
      (fun q => phase τ (fun _ => 0) q * (0 : ℂ)) p = 0
    simp only [mul_zero, iteratedDirectional_zero]
  · change iteratedDirectional (w.map coordinateVector)
      (fun q => phase τ (fun _ => 0) q * (0 : ℂ)) p = 0
    simp only [mul_zero, iteratedDirectional_zero]

namespace Expression

def conjugatedVariationLM {O : Set LowJet} {U : Set Base} {G : Base → Space} {e : Expression}
    (hO : IsOpen O) (hU : IsOpen U) (he : e.SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {φ : Base → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (τ t : ℝ) :
    SupportedField (F := Fin 4 → ℂ) K →ₗ[ℝ] SupportedField (F := ℂ) K :=
  (inversePhaseLM K hφ τ).comp
    ((complexVariationLM hO hU he hG hQ K hKU t).comp (phaseLM K hφ τ))

lemma conjugatedVariationLM_apply {O : Set LowJet} {U : Set Base} {G : Base → Space} {e : Expression}
    (hO : IsOpen O) (hU : IsOpen U) (he : e.SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {φ : Base → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (τ t : ℝ) (H : SupportedField (F := Fin 4 → ℂ) K) (p : Base) :
    conjugatedVariationLM hO hU he hG hQ K hKU hφ τ t H p =
      conjugatedVariation e G (singlePhase φ) (singleDirection H) τ 0 (p, t) := by
  change phase τ (fun q => -φ q) p *
    complexVariationLM hO hU he hG hQ K hKU t (phaseLM K hφ τ H) p = _
  rw [complexVariationLM_apply, phase_neg_inv]
  change (phase τ φ p)⁻¹ * ((ofExpression e).differentiate 0).evalComplex G
    (complexDirectionData G (fun q => phase τ φ q • H q)) (p, t) = _
  rw [← single_oscillatoryData]
  simp only [conjugatedVariation, phaseProduct, singlePhase, Matrix.cons_val_zero]
  simp only [show ¬ (1 : Fin 3) ≤ 0 by decide, show ¬ (2 : Fin 3) ≤ 0 by decide,
    ↓reduceIte, mul_one]
  rfl

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
