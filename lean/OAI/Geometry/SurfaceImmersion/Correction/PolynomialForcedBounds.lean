import OAI.Geometry.SurfaceImmersion.Correction.PolynomialForcedCancellation
import OAI.Geometry.SurfaceImmersion.Geometry.PerturbedForcedSize

namespace OAI

/-! A single actual forced displacement satisfies both its size bound and
its high-order cancellation estimate. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates
variable {n : ℕ} {U : Set Base} {O Q : Set LowJet} {G : Base → Space}

theorem polynomial_forced_real_bounds
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
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      let κ := fun m => max (SmallModes.errorConstant m (C m))
        (D m * SmallModes.initialConstant 4 (m + tensorOrder P) (C (m + tensorOrder P)))
      ∀ (f : SupportedField (F := Fin 3 → ℂ) (modeSupport K)) (q : ℕ),
        ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧
          tsupport X ⊆ (modeSupport K : Set SmallModes.Base) ∧
          (∀ m, WeightedBound Set.univ τ m
            (2 ^ m * SmallModes.forcedModeBudget 4 (tensorOrder P) C D q m *
              supportedWeightedSeminorm (modeSupport K) s
                (m + (q + 1) * (tensorOrder P + 1)) f) X) ∧
          (∀ m, WeightedBound Set.univ τ m
            (2 ^ m * ((τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
              FiniteParametrix.boundProfile (tensorOrder P + 1) κ
                (fun r => κ r * supportedWeightedSeminorm (modeSupport K) s
                  (r + (tensorOrder P + 1)) f) q m))
            (coordinateFullLinearized P ε G X + RealModes.realOsc τ f)) := by
  obtain ⟨D, hD, hd⟩ := coordinatePolynomialOperator_bounds hU hO hQcompact hQO P hP K hKU B hB
  dsimp only
  refine ⟨D, hD, ?_⟩
  intro f q
  let R := coordinatePolynomialOperator hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU τ ε
  have hR := hd G hG hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb
  let Z := SmallModes.perturbedMode τ (coordinateComplexField_smooth hG) hM
    (modeSupport K) (modeSupport_subset K hKU) R (-f) q
  let A := (SmallModes.conjugatedDLM τ (coordinateComplexField_smooth hG) (modeSupport K)).restrictScalars ℝ + R
  let W := A Z + f
  refine ⟨RealModes.realOsc τ Z,
    (contDiffOn_univ.mp (RealModes.contDiffOn_realOsc Z.contDiff.contDiffOn τ)),
    (RealModes.realOsc_tsupport τ Z).trans Z.tsupport_subset, ?_, ?_⟩
  · intro m
    have hb := SmallModes.perturbedMode_size τ (coordinateComplexField_smooth hG) hM
      (modeSupport K) (modeSupport_subset K hKU) hτ hs hτs hs1 hε hsmall C D hC hD hc R hR (-f) q m
    simp only [map_neg_eq_map] at hb
    have hwb := (weightedBound_of_supportedSeminorm s m Z).mono_const hb
    have hsize := RealModes.weighted_realOsc isOpen_univ hτ hτs
      (mul_nonneg (SmallModes.forcedModeBudget_nonneg 4 (tensorOrder P) C D hC q m)
        (apply_nonneg _ _)) Z.contDiff.contDiffOn hwb
    simpa only [mul_assoc] using hsize
  · intro m
    let κ := fun r => max (SmallModes.errorConstant r (C r))
      (D r * SmallModes.initialConstant 4 (r + tensorOrder P) (C (r + tensorOrder P)))
    let η := τ / s + ε / τ ^ tensorLoss P
    let E := η ^ (q + 1) * FiniteParametrix.boundProfile (tensorOrder P + 1) κ
      (fun r => κ r * supportedWeightedSeminorm (modeSupport K) s
        (r + (tensorOrder P + 1)) f) q m
    have hres := SmallModes.perturbedMode_residual_bound τ (coordinateComplexField_smooth hG) hM
      (modeSupport K) (modeSupport_subset K hKU) hτ hs hτs hs1 hε C D hC hD hc R hR (-f) q m
    have hb : supportedWeightedSeminorm (modeSupport K) s m W ≤ E := by
      dsimp only at hres
      simp only [map_neg_eq_map, sub_neg_eq_add, mul_assoc] at hres
      rw [FiniteParametrix.boundProfile_const_mul] at hres
      simpa only [W, Z, A, R, E, η, κ, pow_succ, mul_assoc] using hres
    have hE : 0 ≤ E := (apply_nonneg (supportedWeightedSeminorm (modeSupport K) s m) W).trans hb
    have hr := RealModes.weighted_realOsc isOpen_univ hτ hτs hE W.contDiff.contDiffOn
      ((weightedBound_of_supportedSeminorm s m W).mono_const hb)
    have hi := coordinateFullLinearized_residual hO hU P hP hG (fun _ hp => hQO (hGQ hp))
      K hKU τ ε Z (-f)
    have hn : RealModes.realOsc τ (-f) = -RealModes.realOsc τ f := RealModes.realOsc_neg τ f
    have he : coordinateFullLinearized P ε G (RealModes.realOsc τ Z) + RealModes.realOsc τ f =
        RealModes.realOsc τ W := by simpa only [hn, sub_neg_eq_add] using hi
    rw [he]
    exact hr

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
