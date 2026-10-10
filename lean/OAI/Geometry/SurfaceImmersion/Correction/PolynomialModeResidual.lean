import OAI.Geometry.SurfaceImmersion.Correction.PolynomialModeConstruction
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteParametrixPowers

namespace OAI

/-! The forced linear modes for the polynomially perturbed metric operator
are solved to every fixed finite power of the small parameter. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

variable {n : ℕ} {U : Set Base} {O Q : Set LowJet} {G : Base → Space}

abbrev modeSupport (K : Compacts Base) : Compacts SmallModes.Base :=
  K.map planeCoordinateIsometry planeCoordinateIsometry.continuous

lemma modeSupport_subset (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) :
    (modeSupport K : Set SmallModes.Base) ⊆ planeCoordinateIsometry '' U := by
  rintro p ⟨x, hx, rfl⟩
  exact ⟨x, hKU hx, rfl⟩

theorem polynomial_forced_mode_residual
    (hU : IsOpen U) (hO : IsOpen O) (hQcompact : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ i l, (P i l).SmoothCoeffs O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (hG : ContDiff ℝ ∞ G) (hGQ : Set.MapsTo (lowJet G) U Q)
    (hM : SmallModes.ModeDomain (coordinateComplexField G) (planeCoordinateIsometry '' U))
    {s : ℝ≥0} {τ ε : ℝ} (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s)
    (hs1 : s ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (B C : ℕ → ℝ) (hB : ∀ m, 1 ≤ B m) (hC : ∀ m, 0 ≤ C m)
    (hGb : ∀ m, WeightedBound U s (m + tensorOrder P) (B m) (lowJet G))
    (hc : ∀ m, SmallModes.ReconstructionCoefficientBound (coordinateComplexField G)
      (planeCoordinateIsometry '' U) s (m + 1) (C m)) :
    let R := coordinatePolynomialOperator hO hU P hP hG
      (fun _ hp => hQO (hGQ hp)) K hKU τ ε
    let A := (SmallModes.conjugatedDLM τ (coordinateComplexField_smooth hG) (modeSupport K)).restrictScalars ℝ + R
    let S := (SmallModes.forcedModeLM τ (coordinateComplexField_smooth hG) hM
      (modeSupport K) (modeSupport_subset K hKU) 0).restrictScalars ℝ
    let η := τ / s + ε / τ ^ tensorLoss P
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      let κ := fun m => max (SmallModes.errorConstant m (C m))
        (D m * SmallModes.initialConstant 4 (m + tensorOrder P) (C (m + tensorOrder P)))
      ∀ (f : SupportedField (F := Fin 3 → ℂ) (modeSupport K)) (q m : ℕ),
        supportedWeightedSeminorm (modeSupport K) s m
          (A (FiniteParametrix.improve A S f (S f) q) - f) ≤
        η ^ (q + 1) * FiniteParametrix.boundProfile (tensorOrder P + 1) κ
          (fun r => κ r * supportedWeightedSeminorm (modeSupport K) s (r + (tensorOrder P + 1)) f) q m := by
  obtain ⟨D, hD, hd⟩ := coordinatePolynomialOperator_bounds hU hO hQcompact hQO P hP K hKU B hB
  dsimp only
  refine ⟨D, hD, ?_⟩
  intro f q m
  let R := coordinatePolynomialOperator hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU τ ε
  have hR := hd G hG hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb
  have hdef := SmallModes.perturbed_geometric_defect_bound τ (coordinateComplexField_smooth hG) hM
    (modeSupport K) (modeSupport_subset K hKU) hτ hs hτs hs1 hε C D hC hD hc R hR
  have hη : 0 ≤ τ / s + ε / τ ^ tensorLoss P :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  apply FiniteParametrix.residual_bound_succ _ _ f _
    (fun r => supportedWeightedSeminorm (modeSupport K) s r) _ _ _ hη
  · intro r
    exact (SmallModes.errorConstant_nonneg _ (hC r)).trans (le_max_left _ _)
  · exact hdef
  · intro r
    simpa only [FiniteParametrix.defect, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, R, mul_assoc] using hdef r f

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
