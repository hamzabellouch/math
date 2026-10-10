import OAI.Geometry.SurfaceImmersion.Correction.CoordinatePolynomialRealization

namespace OAI

/-! Exact realization of the full perturbed linear residual in real fields. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open SmallModes

/-- The actual metric derivative plus the actual polynomial derivative,
written in the coordinates used by the finite solver. -/
def coordinateFullLinearized {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (X : RealModes.RField 4) : SmallModes.Base → Fin 3 → ℝ :=
  RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
    coordinateRealLinearized P ε G X 0

lemma coordinateFullLinearized_residual {n : ℕ} {O : Set LowJet} {U : Set Base}
    {G : Base → Space} (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ i l, (P i l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (τ ε : ℝ) (Z : SupportedField (F := Fin 4 → ℂ) (modeSupport K))
    (f : SupportedField (F := Fin 3 → ℂ) (modeSupport K)) :
    let R := coordinatePolynomialOperator hO hU P hP hG hQ K hKU τ ε
    let A := (conjugatedDLM τ (coordinateComplexField_smooth hG) (modeSupport K)).restrictScalars ℝ + R
    coordinateFullLinearized P ε G (RealModes.realOsc τ Z) - RealModes.realOsc τ f =
      RealModes.realOsc τ (A Z - f) := by
  dsimp only
  have hF : ContDiff ℝ ∞ (G ∘ planeCoordinateIsometry.symm) :=
    hG.comp planeCoordinateIsometry.symm.contDiff
  have hp := coordinatePolynomialOperator_realization hO hU P hP hG hQ K hKU τ ε Z
  funext p
  have hm := RealModes.realLinearized_residual (hF.differentiable (by simp) p)
    (Z.contDiff.differentiable (by simp) p) τ f
  change RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm)
      (RealModes.realOsc τ Z) p + coordinateRealLinearized P ε G (RealModes.realOsc τ Z) 0 p -
      RealModes.realOsc τ f p = _
  rw [hp]
  have ha : RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm)
        (RealModes.realOsc τ Z) p +
      RealModes.realOsc τ (coordinatePolynomialOperator hO hU P hP hG hQ K hKU τ ε Z) p -
      RealModes.realOsc τ f p =
      (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm)
        (RealModes.realOsc τ Z) p - RealModes.realOsc τ f p) +
      RealModes.realOsc τ (coordinatePolynomialOperator hO hU P hP hG hQ K hKU τ ε Z) p := by abel
  rw [ha, hm]
  funext i
  change (unitMode τ p * (conjugatedD τ (coordinateComplexField G) Z p i - f p i)).re +
      (unitMode τ p * (coordinatePolynomialOperator hO hU P hP hG hQ K hKU τ ε Z p i)).re =
    (unitMode τ p * (conjugatedD τ (coordinateComplexField G) Z p i +
      coordinatePolynomialOperator hO hU P hP hG hQ K hKU τ ε Z p i - f p i)).re
  simp only [mul_add, mul_sub, Complex.add_re, Complex.sub_re]
  ring


end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
