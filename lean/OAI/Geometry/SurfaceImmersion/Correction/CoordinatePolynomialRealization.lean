import OAI.Geometry.SurfaceImmersion.Correction.PolynomialLinearModes
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialModeResidual

namespace OAI

/-! The coordinate operator used in the finite parametrix really is the
linearization of the polynomial perturbation on real oscillatory fields. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open ModulatedJets

/-- Polynomial first variation in the product coordinates of the metric solver. -/
def coordinateRealLinearized {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (X : RealModes.RField 4) (t : ℝ) : SmallModes.Base → Fin 3 → ℝ :=
  fun p i => linearized (P i) ε G (X ∘ planeCoordinateIsometry) t (planeCoordinateIsometry.symm p)

lemma coordinatePolynomialOperator_realization {n : ℕ} {O : Set LowJet} {U : Set Base}
    {G : Base → Space} (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ i l, (P i l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (τ ε : ℝ) (Z : SupportedField (F := Fin 4 → ℂ) (modeSupport K)) :
    coordinateRealLinearized P ε G (RealModes.realOsc τ Z) 0 =
      RealModes.realOsc τ (coordinatePolynomialOperator hO hU P hP hG hQ K hKU τ ε Z) := by
  let H := (supportedCoordinateEquiv planeCoordinateIsometry K).symm Z
  have hf : RealModes.realOsc τ Z ∘ planeCoordinateIsometry =
      realField (fun x => phase τ firstPhase x • H x) := by
    funext x a
    rfl
  funext p i
  change linearized (P i) ε G (RealModes.realOsc τ Z ∘ planeCoordinateIsometry) 0
      (planeCoordinateIsometry.symm p) =
    (SmallModes.unitMode τ p * conjugatedLM hO hU (P i) (hP i) hG hQ K hKU
      firstPhase_smooth τ ε 0 H (planeCoordinateIsometry.symm p)).re
  rw [hf, conjugatedLM_realization hO hU (P i) (hP i) hG hQ K hKU firstPhase_smooth τ ε 0 H]
  rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
