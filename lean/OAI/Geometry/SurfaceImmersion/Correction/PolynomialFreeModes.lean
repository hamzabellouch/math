import OAI.Geometry.SurfaceImmersion.Correction.PolynomialModeResidual
import OAI.Geometry.SurfaceImmersion.Correction.SupportedFreeLinearity

namespace OAI

/-! Free normal amplitudes for the actual polynomially perturbed metric operator. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

variable {n : ℕ} {U : Set Base} {O Q : Set LowJet} {G : Base → Space}

theorem polynomial_free_mode_bounds
    (hU : IsOpen U) (hO : IsOpen O) (hQcompact : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ i l, (P i l).SmoothCoeffs O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (hG : ContDiff ℝ ∞ G) (hGQ : Set.MapsTo (lowJet G) U Q)
    (hM : SmallModes.ModeDomain (coordinateComplexField G) (planeCoordinateIsometry '' U))
    {s : ℝ≥0} {τ ε : ℝ} (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s)
    (hs1 : s ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (B C : ℕ → ℝ) (hB : ∀ m, 1 ≤ B m) (hC : ∀ m, 0 ≤ C m)
    (hGb : ∀ m, WeightedBound U s (m + tensorOrder P) (B m) (lowJet G))
    (hc : ∀ m, SmallModes.ReconstructionCoefficientBound (coordinateComplexField G)
      (planeCoordinateIsometry '' U) s (m + 1) (C m)) :
    let R := coordinatePolynomialOperator hO hU P hP hG
      (fun _ hp => hQO (hGQ hp)) K hKU τ ε
    let A := (SmallModes.conjugatedDLM τ (coordinateComplexField_smooth hG) (modeSupport K)).restrictScalars ℝ + R
    let η := τ / s + ε / τ ^ tensorLoss P
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      let κ := fun r => max (SmallModes.errorConstant r (C r))
        (D r * SmallModes.initialConstant 4 (r + tensorOrder P) (C (r + tensorOrder P)))
      let γ := fun r => max (SmallModes.fullErrorConstant 4 r (C r))
        (D r * SmallModes.initialConstant 4 (r + tensorOrder P) (C (r + tensorOrder P)))
      ∀ (V : SupportedField (F := Fin 4 → ℂ) (modeSupport K)),
        SmallModes.FreeCoefficient (coordinateComplexField G) (planeCoordinateIsometry '' U) V →
        ∀ q m,
          let Z := SmallModes.perturbedFreeLM τ (coordinateComplexField_smooth hG) hM
            (modeSupport K) (modeSupport_subset K hKU) R q V
          let N := fun r => γ r * supportedWeightedSeminorm (modeSupport K) s (r + (tensorOrder P + 1)) V
          supportedWeightedSeminorm (modeSupport K) s m (A Z) ≤
            η ^ (q + 1) * FiniteParametrix.boundProfile (tensorOrder P + 1) κ N q m ∧
          supportedWeightedSeminorm (modeSupport K) s m (Z - V) ≤
            η * ((∑ i ∈ Finset.range q, SmallModes.initialConstant 4 m (C m) *
              FiniteParametrix.boundProfile (tensorOrder P + 1) κ N i (m + (tensorOrder P + 1))) +
              SmallModes.amplitudeConstant 4 m (C m) *
                supportedWeightedSeminorm (modeSupport K) s (m + (tensorOrder P + 1)) V) := by
  obtain ⟨D, hD, hd⟩ := coordinatePolynomialOperator_bounds hU hO hQcompact hQO P hP K hKU B hB
  dsimp only
  refine ⟨D, hD, ?_⟩
  intro V hV q m
  have hR := hd G hG hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb
  rw [SmallModes.perturbedFreeLM_apply]
  constructor
  · exact SmallModes.perturbedFreeMode_residual_bound τ (coordinateComplexField_smooth hG) hM
      (modeSupport K) (modeSupport_subset K hKU) hτ hs hτs hs1 hε C D hC hD hc _ hR V
      hV.perpX hV.perpY hV.perpSecond q m
  · exact SmallModes.perturbedFreeMode_near_seed τ (coordinateComplexField_smooth hG) hM
      (modeSupport K) (modeSupport_subset K hKU) hτ hs hτs hs1 hε hsmall C D hC hD hc _ hR V
      hV.perpX hV.perpY hV.perpSecond q m

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
