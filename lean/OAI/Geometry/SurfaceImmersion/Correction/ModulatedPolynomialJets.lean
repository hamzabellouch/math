import OAI.Geometry.SurfaceImmersion.Atlas.WeightedComplexMixedJets
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedModulatedJets

namespace OAI

/-! Actual oscillatory direction jets factor into one phase per direction
and a slow amplitude jet. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression

namespace MixedExpression

lemma scaleJets_base (J : JetData) (c : Fin 3 → Base → ℂ) (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    scaleJets J c 0 w a p = J 0 w a p := by
  simp [scaleJets, scaleJetSlot]

lemma scaleJets_succ (J : JetData) (c : Fin 3 → Base → ℂ) (j : Fin 3)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    scaleJets J c j.succ w a p = c j p * J j.succ w a p := by
  fin_cases j <;> simp [scaleJets, scaleJetSlot]

end MixedExpression
namespace ModulatedJets

abbrev DirectionFields := Fin 3 → Base → Fin 4 → ℂ

def amplitudeData (G : Base → Space) (φ : Fin 3 → Base → ℝ)
    (H : DirectionFields) (τ : ℝ) : JetData :=
  Fin.cases (fun w a p => (jet G w a p : ℂ))
    (fun j w a => amplitudeJet τ (φ j) (w.map coordinateVector) (fun p => H j p a))

def oscillatoryData (G : Base → Space) (φ : Fin 3 → Base → ℝ)
    (H : DirectionFields) (τ : ℝ) : JetData :=
  Fin.cases (fun w a p => (jet G w a p : ℂ))
    (fun j w a => iteratedDirectional (w.map coordinateVector)
      (fun p => phase τ (φ j) p * H j p a))

lemma amplitudeData_base (G : Base → Space) (φ : Fin 3 → Base → ℝ)
    (H : DirectionFields) (τ : ℝ) (w : List (Fin 2)) (a : Fin 4) :
    amplitudeData G φ H τ 0 w a = fun p => (jet G w a p : ℂ) := rfl

lemma amplitudeData_succ (G : Base → Space) (φ : Fin 3 → Base → ℝ)
    (H : DirectionFields) (τ : ℝ) (j : Fin 3) (w : List (Fin 2)) (a : Fin 4) :
    amplitudeData G φ H τ j.succ w a =
      amplitudeJet τ (φ j) (w.map coordinateVector) (fun p => H j p a) := rfl

lemma oscillatoryData_factor (G : Base → Space) {φ : Fin 3 → Base → ℝ}
    {H : DirectionFields} (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (τ : ℝ) :
    oscillatoryData G φ H τ = scaleJets (amplitudeData G φ H τ) (fun j => phase τ (φ j)) := by
  funext i w a p
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (scaleJets_base (amplitudeData G φ H τ) (fun j => phase τ (φ j)) w a p).symm
  · rw [scaleJets_succ]
    exact congrFun (iterated_phase_product (hφ j) (contDiff_pi.mp (hH j) a)
      τ (w.map coordinateVector)) p

lemma amplitudeData_smooth {G : Base → Space} {φ : Fin 3 → Base → ℝ}
    {H : DirectionFields} (hG : ContDiff ℝ ∞ G) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (τ : ℝ) :
    ∀ i w a, ContDiff ℝ ∞ (amplitudeData G φ H τ i w a) := by
  intro i w a
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Complex.ofRealCLM.contDiff.comp (jet_smooth hG w a)
  · exact amplitudeJet_smooth (hφ j) (contDiff_pi.mp (hH j) a) τ (w.map coordinateVector)

/-- Exact phase cancellation for each of the first three complexified
variations. The remaining factors are the modulated amplitude jets. -/
theorem variation_phase_factor (e : Expression) (G : Base → Space) {φ : Fin 3 → Base → ℝ}
    {H : DirectionFields} (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (τ : ℝ) (z : Base × ℝ) (i : Fin 3) :
    (e.variations i).evalComplex G (oscillatoryData G φ H τ) z =
      (phase τ (φ 0) z.1 * (if 1 ≤ i then phase τ (φ 1) z.1 else 1) *
        (if 2 ≤ i then phase τ (φ 2) z.1 else 1)) *
      (e.variations i).evalComplex G (amplitudeData G φ H τ) z := by
  rw [oscillatoryData_factor G hφ hH τ]
  have h := evalComplex_scaleJets (fun j => e.variations_degree i j) G
    (amplitudeData G φ H τ) (fun j => phase τ (φ j)) z
  fin_cases i <;> simpa using h

end ModulatedJets
end ClosedSurfaceR4.JetPolynomial

end

end OAI
