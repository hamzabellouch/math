import OAI.Probability.SLE.Geometry.SpatialExhaustion
import OAI.Probability.SLE.SausageCharge

namespace OAI

/-! Turning one-mesh sausage charges into upper Hausdorff expectations. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

/-- A shrinking cover whose selected part is charged to a single sausage
mesh and whose expected residual cost vanishes has the desired uniform
Hausdorff expectation bound. The hypothesis describes actual covers. -/
theorem expected_hausdorff_le_of_sausage_charged_covers
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (h : ℝ → ℝ) (hh : IsGauge h) (E : Ω → Set ℂ)
    (U : ℕ → Ω → ℕ → Set ℂ) (δ : ℕ → ℝ≥0∞)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hcover : ∀ᵐ ω ∂P, ∀ n, E ω ⊆ ⋃ j, U n ω j)
    (hdiam : ∀ᵐ ω ∂P, ∀ n j, ediam (U n ω j) ≤ δ n)
    (hmeas : ∀ n, AEMeasurable
      (fun ω => ∑' j, extendedGauge h (ediam (U n ω j))) P)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (R : ℝ) (C : ℝ≥0)
    (error : ℕ → Ω → ℝ≥0∞) (herr : ∀ n, AEMeasurable (error n) P)
    (herrlim : Tendsto (fun n => ∫⁻ ω, error n ω ∂P) atTop (𝓝 0))
    (hcharge : ∀ n, ∀ᵐ ω ∂P,
      (∑' j, extendedGauge h (ediam (U n ω j))) ≤
        (C : ℝ≥0∞) * wholeSausageCharge κ (γ ω) (v n) (closedBall 0 R) + error n ω) :
    (∫⁻ ω, hausdorffGauge h (E ω) ∂P) ≤
      (C : ℝ≥0∞) * wholeSausageChargeBound κ R := by
  obtain ⟨_, hsausage⟩ := source_cover_charge P κ hκ hκ8 γ hSLE R
  have hcost (n : ℕ) :
      (∫⁻ ω, ∑' j, extendedGauge h (ediam (U n ω j)) ∂P) ≤
        (C : ℝ≥0∞) * wholeSausageChargeBound κ R + ∫⁻ ω, error n ω ∂P := by
    calc
      _ ≤ ∫⁻ ω, (C : ℝ≥0∞) *
          wholeSausageCharge κ (γ ω) (v n) (closedBall 0 R) + error n ω ∂P :=
        lintegral_mono_ae (hcharge n)
      _ = (C : ℝ≥0∞) * (∫⁻ ω,
          wholeSausageCharge κ (γ ω) (v n) (closedBall 0 R) ∂P) +
          ∫⁻ ω, error n ω ∂P := by
        rw [lintegral_add_right' _ (herr n),
          lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      _ ≤ _ := add_le_add (mul_le_mul' le_rfl (hsausage (v n) (hv n)).2) le_rfl
  apply expected_hausdorff_le_of_shrinking_covers P h hh E U δ hδ
    hcover hdiam hmeas
  have ht : Tendsto (fun n => (C : ℝ≥0∞) * wholeSausageChargeBound κ R +
      ∫⁻ ω, error n ω ∂P) atTop
      (𝓝 ((C : ℝ≥0∞) * wholeSausageChargeBound κ R)) := by
    simpa only [add_zero] using tendsto_const_nhds.add herrlim
  exact (liminf_le_liminf (Eventually.of_forall hcost)).trans_eq ht.liminf_eq

end SLEExactGauge

end

end OAI
