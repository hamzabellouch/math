import OAI.Geometry.SurfaceImmersion.Correction.LocalCombinedMean
import OAI.Geometry.Immersion.ClosedSurface.FreeAmplitude

namespace OAI

/-! Identify the actual local quadratic zero phase with the leading tensor
plus the combined mean correction. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open RealModes WeightedEstimates
open PhaseMean (firstDirection secondDirection)
variable {n : ℕ} {F : RField 4} {V : Set SmallModes.Base}

def seedQuadraticMeanTensor (P : Fin 3 → Fin n → Expression) (δ τ ε : ℝ) (G : Base → Space)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V)
    (R : SupportedField (F := SmallModes.Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K))
    (q : ℕ) (b : SupportedField (F := ℝ) (modeSupport K)) (x : Base) : Fin 3 → ℝ :=
  let Z := correctedNormalSeed δ τ hF h (modeSupport K) hKV R q b
  let H := coordinateCorrectedSeed δ τ hF h K hKV R q b
  fun i => QuadraticMean.zeroPair
      (SmallModes.gradientAmplitude τ Z (firstDirection i) (planeCoordinateIsometry x))
      (SmallModes.gradientAmplitude τ Z (secondDirection i) (planeCoordinateIsometry x)) +
    quadraticMeanCoefficient (P i) ε G firstPhase H τ 0 x

lemma seedQuadraticMeanTensor_eq (P : Fin 3 → Fin n → Expression) (δ τ ε : ℝ)
    (hδ : δ ≠ 0) (hτ : τ ≠ 0) (G : Base → Space)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V)
    (R : SupportedField (F := SmallModes.Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K))
    (q : ℕ) (b : SupportedField (F := ℝ) (modeSupport K)) (x : Base)
    (hx : planeCoordinateIsometry x ∈ V) :
    seedQuadraticMeanTensor P δ τ ε G hF h K hKV R q b x =
      δ ^ 2 • ((fun i => b (planeCoordinateIsometry x) ^ 2 * (firstDirection i).1 * (secondDirection i).1) +
        combinedMeanTensor P δ τ ε G hF h K hKV R q b x) := by
  funext i
  exact combined_seed_mean_identity (P i) δ τ ε hδ hτ G hF h K hKV R q b
    (firstDirection i) (secondDirection i) x hx

end ClosedSurfaceR4.JetPolynomial.Perturbation

namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates FiniteMean
open JetPolynomial (SupportedField)
open JetPolynomial.Perturbation (modeSupport seedQuadraticMeanTensor)
variable {n : ℕ} {U V : Set Base} {s r ρ R₀ : ℝ} {reference : Base → Tensor}
  {F : RField 4} {K : Compacts JetPolynomial.Base}
  {ψ : SupportedField (F := ℝ) (modeSupport K)}
  {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

def localQuadraticMean (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (hρ : 0 < ρ) (hKV : (modeSupport K : Set Base) ⊆ V)
    (P : Fin 3 → Fin n → JetPolynomial.Expression) (G : JetPolynomial.Base → JetPolynomial.Space)
    (δ τ ε : ℝ) (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K)) (q : ℕ) (A : Base → Tensor) : Base → Tensor :=
  fun x => pullbackField χ x (seedQuadraticMeanTensor P δ τ ε G h.smoothF h.domain K hKV R q
    (supportedTrialAmplitude h hρ hKV A) (JetPolynomial.planeCoordinateIsometry.symm (χ x)))

lemma localQuadraticMean_eq (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (hρ : 0 < ρ) (hKV : (modeSupport K : Set Base) ⊆ V)
    (P : Fin 3 → Fin n → JetPolynomial.Expression) (G : JetPolynomial.Base → JetPolynomial.Space)
    (δ τ ε : ℝ) (hδ : δ ≠ 0) (hτ : τ ≠ 0)
    (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K)) (q : ℕ) {A : Base → Tensor}
    (hA : ContDiffOn ℝ ∞ A U) (hball : InTrialBall U reference r A)
    {x : Base} (hx : x ∈ U) :
    localQuadraticMean h hρ hKV P G δ τ ε R q A x =
      δ ^ 2 • (chartLeadingTensor (phaseAmplitude ψ (coefficient Q e A)) χ x +
        localCombinedMean h hρ hKV P G δ τ ε R q A x) := by
  have hpoint : JetPolynomial.planeCoordinateIsometry (JetPolynomial.planeCoordinateIsometry.symm (χ x)) ∈ V := by
    rw [JetPolynomial.planeCoordinateIsometry.apply_symm_apply]
    exact h.chiInto hx
  dsimp only [localQuadraticMean]
  rw [JetPolynomial.Perturbation.seedQuadraticMeanTensor_eq P δ τ ε hδ hτ G h.smoothF h.domain K hKV R q
    (supportedTrialAmplitude h hρ hKV A) _ hpoint, map_smul, map_add]
  congr 1
  apply congrArg₂ (· + ·)
  · unfold chartLeadingTensor
    congr 1
    funext i
    rw [JetPolynomial.planeCoordinateIsometry.apply_symm_apply,
      supportedTrialAmplitude_apply h hρ hKV hA hball]
  · rfl

end ClosedSurfaceR4.PhaseMean

end

end OAI
