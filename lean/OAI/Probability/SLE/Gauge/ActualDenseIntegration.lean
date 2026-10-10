import OAI.Probability.SLE.Gauge.CanonicalDenseIntegration
import OAI.Probability.SLE.Gauge.RestartDenseWeight

namespace OAI

/-! Actual physical stopped-mass probabilities from the proved canonical
sections and the actual normalized restarted witnesses. All restrictions on
the old marked state lie in the stopped past. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open FrontSuccessMeasurability

local instance actualDenseIntegrationRealMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance actualDenseIntegrationRealBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance actualDenseIntegrationComplexMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance actualDenseIntegrationComplexBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem actual_dense_sections_integrate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (ν : Measure C(ℝ≥0, ℝ)) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (Y : Ω → C(ℝ≥0, ℝ)) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω C(ℝ≥0, ℝ) mΩ _ Y (P.restrict A) = P A • ν)
    (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ)) (hΦ : Measurable Φ)
    (Fb : Ω → C(closedHalfPlane, ℂ)) (hFb : Measurable[m] Fb)
    (τ a : Ω → ℝ≥0) (ha : ∀ ω, 0 < a ω)
    (Gc Fc : Ω → ℝ≥0 → ℂ → ℂ)
    (hb : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (normalizedRestartDriver (fun t => Real.sqrt κ * B t ω) (τ ω) (a ω))
      (Φ (Y ω)) (Gc ω) (Fc ω))
    (hdriver : ∀ ω, (fun t => Real.sqrt κ * Y ω t) =
      normalizedRestartDriver (fun t => Real.sqrt κ * B t ω) (τ ω) (a ω))
    (hpath : ∀ᵐ ω ∂P, ∀ t, finiteBoundaryPath (Fb ω) (Φ (Y ω)) t =
      γ ω (τ ω + (a ω) ^ 2 * t))
    (w : Ω → ℂ) (hwm : Measurable[m] w)
    (E : Set Ω) (hE : MeasurableSet[m] E) (hwH : ∀ ω ∈ E, w ω ∈ upperHalfPlane)
    (z : ℂ) (u q b r v : ℝ) (hq : 0 ≤ q) (N : ℕ)
    (hpoint : ∀ ω ∈ E,
      F ω (τ ω) ((a ω : ℂ) * w ω + (Real.sqrt κ * B (τ ω) ω : ℝ)) = z)
    (hbase : ∀ ω ∈ E, fullRadius (G ω) (τ ω) z = (2 * z.im) * Real.exp (-u))
    (M : Ω → ℝ≥0∞) (hM : Measurable[m] M) (hMfinite : ∀ ω, M ω ≠ ∞)
    (hMactual : ∀ᵐ ω ∂P, ω ∈ E → M ω = ENNReal.ofReal
      (greenDensity κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (τ ω) z / initialGreen κ z))
    (p : ℝ≥0∞) (hp : p ≠ ∞)
    (hsections : ∀ ω ∈ E, p ≤
      (ν.withDensity (fun y => canonicalFiniteDensity κ (q, w ω, y)))
        (canonicalDenseEvent κ Φ (Fb ω) q (w ω) b r N v z))
    (hS : MeasurableSet[mΩ] (stoppedMassTest κ v (sourceTracePath γ (fun ω => (hw ω).1))
      (fun ω => radiusLevelTime (γ ω) (G ω) z (u + q))
      (closedBall z r) (b * r ^ dimension κ * (N : ℝ) ^ codimension κ)))
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    p * (∫⁻ ω in A ∩ E, M ω ∂P) ≤
      @finiteCenteredLaw Ω mΩ P κ B γ G z (u + q)
        (A ∩ stoppedMassTest κ v (sourceTracePath γ (fun ω => (hw ω).1))
          (fun ω => radiusLevelTime (γ ω) (G ω) z (u + q))
          (closedBall z r) (b * r ^ dimension κ * (N : ℝ) ^ codimension κ)) := by
  classical
  let : MeasurableSpace Ω := mΩ
  let S := stoppedMassTest κ v (sourceTracePath γ (fun ω => (hw ω).1))
    (fun ω => radiusLevelTime (γ ω) (G ω) z (u + q))
    (closedBall z r) (b * r ^ dimension κ * (N : ℝ) ^ codimension κ)
  let Z : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z (u + q) / initialGreen κ z)
  apply canonical_dense_sections_integrate P ν m hm Y hY hlaw κ b r v q N z Φ hΦ Fb hFb
    w hwm E hE M hM hMfinite p hp hsections Z S hS _ A hA
  filter_upwards [hb, hpath, hMactual] with ω hω hpathω hMω hωE
  have hpt := hpoint ω hωE
  have hbaseω : fullRadius (G ω) (τ ω)
      (F ω (τ ω) ((a ω : ℂ) * w ω + (Real.sqrt κ * B (τ ω) ω : ℝ))) =
      (2 * (F ω (τ ω) ((a ω : ℂ) * w ω + (Real.sqrt κ * B (τ ω) ω : ℝ))).im) *
        Real.exp (-u) := by simpa only [hpt] using hbase ω hωE
  have hbound := (hw ω).normalized_restart_dense_weight_le ((hc ω).const_mul _) (τ ω) (a ω)
    (ha ω) κ Φ (Y ω) hω (hdriver ω) (w ω) (hwH ω hωE) u q hq hbaseω
    (Fb ω) hpathω b r v N
  rw [hpt, ← hMω hωE] at hbound
  split_ifs at hbound with hs
  · rw [indicator_of_mem (show ω ∈ S from hs)]
    exact hbound
  · rw [indicator_of_notMem (show ω ∉ S from hs)]
    exact hbound

end SLEExactGauge

end

end OAI
