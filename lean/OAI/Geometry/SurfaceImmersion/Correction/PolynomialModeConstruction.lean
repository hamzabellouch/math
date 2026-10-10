import OAI.Geometry.SurfaceImmersion.Geometry.TensorPerturbationOperator
import OAI.Geometry.SurfaceImmersion.Geometry.SupportedOperatorTransport
import OAI.Geometry.SurfaceImmersion.Geometry.GeometricPerturbedParametrix

namespace OAI

/-! Insert the actual tensor-valued polynomial perturbation into the
geometric finite correction, using the fixed first-coordinate phase. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

abbrev firstPhase : Base → ℝ := fun p => p 0

lemma firstPhase_smooth : ContDiff ℝ ∞ firstPhase :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).contDiff

lemma firstPhase_derivative_bound (U : Set Base) (s : ℝ) (m : ℕ) (v : Fin 2) :
    WeightedBound U s m 1 (fun p => fderiv ℝ firstPhase p (coordinateVector v)) := by
  have he : (fun p => fderiv ℝ firstPhase p (coordinateVector v)) =
      fun _ : Base => coordinateVector v 0 := by
    funext p
    exact congrArg (fun L : Base →L[ℝ] ℝ => L (coordinateVector v))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).fderiv
  rw [he]
  apply (weightedBound_const U s m (coordinateVector v 0)).mono_const
  exact (norm_le_pi_norm (coordinateVector v) 0).trans (norm_coordinateVector_le v)

def coordinateComplexField (G : Base → Space) : SmallModes.Field 4 :=
  fun p => RealModes.complexify (G (planeCoordinateIsometry.symm p))

lemma coordinateComplexField_smooth {G : Base → Space} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (coordinateComplexField G) :=
  (RealModes.complexifyCLM 4).contDiff.comp (hG.comp planeCoordinateIsometry.symm.contDiff)

namespace Perturbation

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

def coordinatePolynomialOperator (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ i l, (P i l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (τ ε : ℝ) :
    SupportedField (F := Fin 4 → ℂ) (K.map planeCoordinateIsometry planeCoordinateIsometry.continuous) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (K.map planeCoordinateIsometry planeCoordinateIsometry.continuous) :=
  transportSupportedLM planeCoordinateIsometry K
    (tensorConjugatedLM hO hU P hP hG hQ K hKU firstPhase_smooth τ ε 0)

/-- The constants may depend on the requested norm, whereas `tensorLoss P`
is fixed before the finite correction depth is chosen. -/
theorem coordinatePolynomialOperator_bounds {Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQcompact : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ i l, (P i l).SmoothCoeffs O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (B : ℕ → ℝ) (hB : ∀ m, 1 ≤ B m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧ ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G)
      (hGQ : Set.MapsTo (lowJet G) U Q) (s : ℝ≥0) (τ ε : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      (∀ m, WeightedBound U s (m + tensorOrder P) (B m) (lowJet G)) →
      ∀ m H, supportedWeightedSeminorm
        (K.map planeCoordinateIsometry planeCoordinateIsometry.continuous) s m
        (coordinatePolynomialOperator hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU τ ε H) ≤
      ε / τ ^ tensorLoss P * D m * supportedWeightedSeminorm
        (K.map planeCoordinateIsometry planeCoordinateIsometry.continuous) s (m + tensorOrder P) H := by
  have hex := fun m => tensorConjugatedLM_bound hU hO hQcompact hQO P hP K hKU m (B m) 1 (hB m) zero_le_one
  choose D hD hd using hex
  refine ⟨D, hD, ?_⟩
  intro G hG hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb m H
  have hlocal := hd m G firstPhase hG firstPhase_smooth hGQ s τ ε hτ hs hτs hs1 hε hε1
    (hGb m) (firstPhase_derivative_bound U s (m + tensorOrder P)) 0 (by simp)
  have htrans := transportSupportedLM_bound planeCoordinateIsometry K
    (tensorConjugatedLM hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU firstPhase_smooth τ ε 0)
    hs m (m + tensorOrder P) (D m * ε / τ ^ tensorLoss P) hlocal H
  change supportedWeightedSeminorm _ s m
    (transportSupportedLM planeCoordinateIsometry K _ H) ≤ _
  convert htrans using 1
  ring

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
