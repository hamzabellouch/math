import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartRealization
import OAI.Geometry.Immersion.ClosedSurface.UniformMean

namespace OAI

/-! The local phase-coordinate polynomial operator keeps the original
fixed scale exponent and derivative loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

variable {n : ℕ} {U : Set Base} {O Q : Set LowJet}

theorem phaseChartPolynomialOperator_bounds
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (B F J I : ℕ → ℝ) (hB : ∀ m, 1 ≤ B m) (hF : ∀ m, 0 ≤ F m)
    (hJ : ∀ m, 1 ≤ J m) (hI : ∀ m, 1 ≤ I m)
    (hebound : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m)
    (hibound : ∀ m j, 1 ≤ j → j ≤ m + 1 → ∀ x ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ I m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
      (hGQ : Set.MapsTo (lowJet G) U Q) (s : ℝ≥0) (τ ε : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      (∀ m, WeightedBound U s (m + tensorOrder P) (B m) (lowJet G)) →
      (∀ m v, WeightedBound U s (m + tensorOrder P) (F m)
        (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ m Z, supportedWeightedSeminorm (chartSupport e (modeSupport K) hKe) s m
        (phaseChartPolynomialOperator hO hU P hP hG (fun _ hp => hQO (hGQ hp))
          K hKU hφ τ ε e he hi hKe Z) ≤
        ε / τ ^ tensorLoss P * D m *
          supportedWeightedSeminorm (chartSupport e (modeSupport K) hKe) s (m + tensorOrder P) Z := by
  obtain ⟨D,hD,hd⟩ := phaseCoordinatePolynomialOperator_bounds hU hO hQ hQO P hP K hKU B F hB hF
  let E := fun m => tensorChartBudget m (I m) (I m) * D m *
    (((m + tensorOrder P).factorial : ℝ) * J (m + tensorOrder P) ^ (m + tensorOrder P))
  have hI0 (m : ℕ) : 0 ≤ I m := zero_le_one.trans (hI m)
  have hJ0 (m : ℕ) : 0 ≤ J m := zero_le_one.trans (hJ m)
  refine ⟨E,fun m => mul_nonneg (mul_nonneg (tensorChartBudget_nonneg m (hI0 m) (hI0 m)) (hD m))
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hJ0 _) _)),?_⟩
  intro G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb m Z
  have hDm := hD m
  have hR := hd G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb m
  have hfield := RealModes.weighted_coordDeriv_of_jets e.open_target hi s.coe_nonneg hs1
    (hI0 m) (hibound m)
  have hb := chartTensorTransportLM_bound e (modeSupport K) hKe he hi
    (phaseCoordinatePolynomialOperator hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε)
    hs hs1 (hJ (m + tensorOrder P)) (hI m) (hI0 m) (by positivity)
    (hebound (m + tensorOrder P))
    (fun j hj hjm => hibound m j hj (hjm.trans (Nat.le_succ m))) hfield hR Z
  change supportedWeightedSeminorm _ s m (chartTensorTransportLM e (modeSupport K) hKe he hi _ Z) ≤ _
  convert hb using 1
  dsimp only [E]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
