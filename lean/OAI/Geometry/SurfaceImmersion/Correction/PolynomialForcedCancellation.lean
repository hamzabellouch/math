import OAI.Geometry.SurfaceImmersion.Correction.CoordinateLinearizedResidual

namespace OAI

/-! Actual real forced cancellation for the polynomially perturbed metric.
The exponent is fixed before the requested finite correction accuracy. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates
variable {n : ℕ} {U : Set Base} {O Q : Set LowJet} {G : Base → Space}

theorem polynomial_forced_real_cancellation
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
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      let κ := fun m => max (SmallModes.errorConstant m (C m))
        (D m * SmallModes.initialConstant 4 (m + tensorOrder P) (C (m + tensorOrder P)))
      ∀ (f : SupportedField (F := Fin 3 → ℂ) (modeSupport K)) (q : ℕ),
        ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧
          tsupport X ⊆ (modeSupport K : Set SmallModes.Base) ∧
          ∀ m, WeightedBound Set.univ τ m
            (2 ^ m * ((τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
              FiniteParametrix.boundProfile (tensorOrder P + 1) κ
                (fun r => κ r * supportedWeightedSeminorm (modeSupport K) s
                  (r + (tensorOrder P + 1)) f) q m))
            (coordinateFullLinearized P ε G X + RealModes.realOsc τ f) := by
  obtain ⟨D, hD, hd⟩ := polynomial_forced_mode_residual hU hO hQcompact hQO P hP K hKU
    hG hGQ hM hτ hs hτs hs1 hε hε1 B C hB hC hGb hc
  dsimp only at hd ⊢
  refine ⟨D, hD, ?_⟩
  intro f q
  let R := coordinatePolynomialOperator hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU τ ε
  let A := (SmallModes.conjugatedDLM τ (coordinateComplexField_smooth hG) (modeSupport K)).restrictScalars ℝ + R
  let S := (SmallModes.forcedModeLM τ (coordinateComplexField_smooth hG) hM
    (modeSupport K) (modeSupport_subset K hKU) 0).restrictScalars ℝ
  let Z := FiniteParametrix.improve A S (-f) (S (-f)) q
  let W := A Z + f
  refine ⟨RealModes.realOsc τ Z,
    (contDiffOn_univ.mp (RealModes.contDiffOn_realOsc Z.contDiff.contDiffOn τ)),
    (RealModes.realOsc_tsupport τ Z).trans Z.tsupport_subset, ?_⟩
  intro m
  let κ := fun r => max (SmallModes.errorConstant r (C r))
    (D r * SmallModes.initialConstant 4 (r + tensorOrder P) (C (r + tensorOrder P)))
  let E := (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
    FiniteParametrix.boundProfile (tensorOrder P + 1) κ
      (fun r => κ r * supportedWeightedSeminorm (modeSupport K) s
        (r + (tensorOrder P + 1)) f) q m
  have hb : supportedWeightedSeminorm (modeSupport K) s m W ≤ E := by
    simpa only [W, sub_neg_eq_add, map_neg_eq_map] using hd (-f) q m
  have hE : 0 ≤ E := (apply_nonneg (supportedWeightedSeminorm (modeSupport K) s m) W).trans hb
  have hwb := (weightedBound_of_supportedSeminorm s m W).mono_const hb
  have hr := RealModes.weighted_realOsc isOpen_univ hτ hτs hE W.contDiff.contDiffOn hwb
  have hi := coordinateFullLinearized_residual hO hU P hP hG (fun _ hp => hQO (hGQ hp))
    K hKU τ ε Z (-f)
  have hn : RealModes.realOsc τ (-f) = -RealModes.realOsc τ f := RealModes.realOsc_neg τ f
  have he : coordinateFullLinearized P ε G (RealModes.realOsc τ Z) + RealModes.realOsc τ f =
      RealModes.realOsc τ W := by
    simpa only [hn, sub_neg_eq_add] using hi
  rw [he]
  exact hr

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
