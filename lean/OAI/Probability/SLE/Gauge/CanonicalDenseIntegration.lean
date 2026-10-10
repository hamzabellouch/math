import OAI.Probability.SLE.Gauge.CanonicalDenseSections
import OAI.Probability.SLE.Geometry.RestartWeightedKernel

namespace OAI

/-! Integration of the proved canonical dense sections over a genuinely
random stopped past. The actual Loewner comparison supplies the final
density domination; there is no independence assumption between tests. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance denseIntegrationRealMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance denseIntegrationRealBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance denseIntegrationComplexMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance denseIntegrationComplexBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem canonical_dense_sections_integrate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (ν : Measure C(ℝ≥0, ℝ)) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → C(ℝ≥0, ℝ)) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω C(ℝ≥0, ℝ) mΩ _ Y (P.restrict A) = P A • ν)
    (κ b r v u : ℝ) (N : ℕ) (z : ℂ)
    (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ)) (hΦ : Measurable Φ)
    (Fb : Ω → C(closedHalfPlane, ℂ)) (hFb : Measurable[m] Fb)
    (w : Ω → ℂ) (hw : Measurable[m] w)
    (E : Set Ω) (hE : MeasurableSet[m] E)
    (M : Ω → ℝ≥0∞) (hM : Measurable[m] M) (hMfinite : ∀ ω, M ω ≠ ∞)
    (q : ℝ≥0∞) (hq : q ≠ ∞)
    (hsections : ∀ ω ∈ E, q ≤
      (ν.withDensity (fun p => canonicalFiniteDensity κ (u, w ω, p)))
        (canonicalDenseEvent κ Φ (Fb ω) u (w ω) b r N v z))
    (Z : Ω → ℝ≥0∞) (S : Set Ω) (hS : MeasurableSet[mΩ] S)
    (hactual : ∀ᵐ ω ∂P, ω ∈ E →
      (canonicalDenseEvent κ Φ (Fb ω) u (w ω) b r N v z).indicator
        (fun p => M ω * canonicalFiniteDensity κ (u, w ω, p)) (Y ω) ≤ S.indicator Z ω)
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    q * (∫⁻ ω in A ∩ E, M ω ∂P) ≤ P.withDensity Z (A ∩ S) := by
  let : MeasurableSpace Ω := mΩ
  let C : Set (Ω × C(ℝ≥0, ℝ)) :=
    {p | p.1 ∈ E ∧ p.2 ∈ canonicalDenseEvent κ Φ (Fb p.1) u (w p.1) b r N v z}
  let K : Ω × C(ℝ≥0, ℝ) → ℝ≥0∞ :=
    fun p => M p.1 * canonicalFiniteDensity κ (u, w p.1, p.2)
  have hC : @MeasurableSet (Ω × C(ℝ≥0, ℝ)) (m.prod _) C :=
    (hE.preimage measurable_fst).inter
      (@measurableSet_canonicalDenseEvent_product Ω m κ b v N Φ hΦ Fb hFb
        (fun _ => u) measurable_const w hw (fun _ => r) measurable_const
        (fun _ => z) measurable_const)
  have hK : @Measurable (Ω × C(ℝ≥0, ℝ)) ℝ≥0∞ (m.prod _) _ K :=
    (hM.comp measurable_fst).mul ((canonicalFiniteDensity_measurable κ).comp
      (measurable_const.prodMk ((hw.comp measurable_fst).prodMk measurable_snd)))
  have hsec : ∀ᵐ ω ∂P, q * E.indicator M ω ≤ ∫⁻ p, C.indicator K (ω, p) ∂ν := by
    apply Eventually.of_forall
    intro ω
    by_cases hω : ω ∈ E
    · have hf : (fun p => C.indicator K (ω, p)) =
          fun p => M ω * (canonicalDenseEvent κ Φ (Fb ω) u (w ω) b r N v z).indicator
            (fun p => canonicalFiniteDensity κ (u, w ω, p)) p := by
        funext p
        by_cases hp : p ∈ canonicalDenseEvent κ Φ (Fb ω) u (w ω) b r N v z <;>
          simp [C, K, hω, hp]
      rw [hf, lintegral_const_mul' _ _ (hMfinite ω), indicator_of_mem hω]
      rw [lintegral_indicator (measurableSet_canonicalDenseEvent κ b r v N Φ hΦ (Fb ω) u (w ω) z),
        ← withDensity_apply]
      · simpa only [mul_comm q] using mul_le_mul' le_rfl (hsections ω hω)
      · exact measurableSet_canonicalDenseEvent κ b r v N Φ hΦ (Fb ω) u (w ω) z
    · simp [C, hω]
  have hdom : ∀ᵐ ω ∂P, C.indicator K (ω, Y ω) ≤ S.indicator Z ω := by
    filter_upwards [hactual] with ω hω
    by_cases hωE : ω ∈ E
    · have he : C.indicator K (ω, Y ω) =
          (canonicalDenseEvent κ Φ (Fb ω) u (w ω) b r N v z).indicator
            (fun p => M ω * canonicalFiniteDensity κ (u, w ω, p)) (Y ω) := by
        by_cases hp : Y ω ∈ canonicalDenseEvent κ Φ (Fb ω) u (w ω) b r N v z <;>
          simp [C, K, hωE, hp]
      rw [he]
      exact hω hωE
    · simp [C, hωE]
  have h := restart_weighted_event_lower_bound P ν m hm Y hY hlaw K hK C hC
    (E.indicator M) Z q hq S hS hsec hdom A hA
  rw [setLIntegral_indicator (hm E hE), inter_comm E A] at h
  exact h

end SLEExactGauge

end

end OAI
