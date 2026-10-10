import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateQuadraticExpansion
import OAI.Geometry.SurfaceImmersion.Atlas.TensorChartBounds

namespace OAI

/-! The polynomial conjugation estimate and its real realization for an
arbitrary smooth phase, before changing to a first-coordinate chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates ModulatedJets

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

def phaseCoordinatePolynomialOperator (hO : IsOpen O) (hU : IsOpen U)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε : ℝ) :
    SupportedField (F := Fin 4 → ℂ) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := PhaseMean.ComplexTensor) (modeSupport K) :=
  transportSupportedLM planeCoordinateIsometry K
    (tensorConjugatedLM hO hU P hP hG hQ K hKU hφ τ ε 0)

theorem phaseCoordinatePolynomialOperator_bounds {Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (B F : ℕ → ℝ) (hB : ∀ m, 1 ≤ B m) (hF : ∀ m, 0 ≤ F m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
      (hGQ : Set.MapsTo (lowJet G) U Q) (s : ℝ≥0) (τ ε : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      (∀ m, WeightedBound U s (m + tensorOrder P) (B m) (lowJet G)) →
      (∀ m v, WeightedBound U s (m + tensorOrder P) (F m)
        (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ m Z, supportedWeightedSeminorm (modeSupport K) s m
        (phaseCoordinatePolynomialOperator hO hU P hP hG (fun _ hp => hQO (hGQ hp))
          K hKU hφ τ ε Z) ≤
        ε / τ ^ tensorLoss P * D m * supportedWeightedSeminorm (modeSupport K) s (m + tensorOrder P) Z := by
  have hex (m : ℕ) := tensorConjugatedLM_bound hU hO hQ hQO P hP K hKU m (B m) (F m) (hB m) (hF m)
  choose D hD hd using hex
  refine ⟨D,hD,?_⟩
  intro G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb m Z
  have hl := hd m G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1
    (hGb m) (hφb m) 0 (by simp)
  have ht := transportSupportedLM_bound planeCoordinateIsometry K
    (tensorConjugatedLM hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε 0)
    hs m (m + tensorOrder P) (D m * ε / τ ^ tensorLoss P) hl Z
  change supportedWeightedSeminorm _ s m (transportSupportedLM planeCoordinateIsometry K _ Z) ≤ _
  convert ht using 1
  ring

lemma phaseCoordinatePolynomialOperator_realization
    (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε : ℝ)
    (Z : SupportedField (F := Fin 4 → ℂ) (modeSupport K)) :
    coordinateRealLinearized P ε G (QuadraticMean.displacement τ (coordinatePhase φ) Z) 0 =
      QuadraticMean.displacement τ (coordinatePhase φ)
        (phaseCoordinatePolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε Z) := by
  let H := (supportedCoordinateEquiv planeCoordinateIsometry K).symm Z
  have hf : QuadraticMean.displacement τ (coordinatePhase φ) Z ∘ planeCoordinateIsometry =
      realField (fun x => phase τ φ x • H x) := by
    funext x a
    change (QuadraticMean.phase (φ (planeCoordinateIsometry.symm (planeCoordinateIsometry x)) / τ) *
      Z (planeCoordinateIsometry x) a).re = (phase τ φ x * H x a).re
    rw [planeCoordinateIsometry.symm_apply_apply, coordinate_phase_value]
    rfl
  funext p k
  change linearized (P k) ε G
      (QuadraticMean.displacement τ (coordinatePhase φ) Z ∘ planeCoordinateIsometry) 0
      (planeCoordinateIsometry.symm p) =
    (QuadraticMean.phase (φ (planeCoordinateIsometry.symm p) / τ) *
      conjugatedLM hO hU (P k) (hP k) hG hQ K hKU hφ τ ε 0 H (planeCoordinateIsometry.symm p)).re
  rw [coordinate_phase_value, hf, conjugatedLM_realization hO hU (P k) (hP k) hG hQ K hKU hφ τ ε 0 H]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
