import OAI.Probability.SLE.Mass.CompactSpatialMass
import OAI.Probability.SLE.Geometry.CountablePastBound
import OAI.Probability.SLE.Gauge.ExpectedBadGrid
import OAI.Probability.SLE.Gauge.ExactMomentGauge

namespace OAI

/-! The finite centered-law tests which suffice for the prescribed lower bound.
The half-threshold and the factor two come from actual past-mass detection. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
  (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω = 0)
  (hκ : 0 < κ) (hκ8 : κ < 8) (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))

include C hB hc h0 hκ hκ8 F hw

lemma compact_spatial_bad_charge_of_finite_tests
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (q : ℕ → ℝ≥0) (hq : DenseRange q)
    (K : Set upperHalfPlane) (hK : IsCompact K) (z : ℂ) (r H : ℝ) (hH : 0 < H)
    (A : ℝ≥0∞)
    (hbound : ∀ j, ∀ᶠ n in atTop,
      (∫⁻ x in (Subtype.val : upperHalfPlane → ℂ) ''
          (K ∩ Subtype.val ⁻¹' closedBall z r),
        ENNReal.ofReal (initialGreen κ x) * finiteCenteredLaw P κ B γ G x (u n)
          (finiteStrictPastEvent ((Finset.range j).image q)
            (fun t => {ω | H < (C.process t ω (K ∩ Subtype.val ⁻¹' closedBall z r)).toReal})
            (fun ω => radiusLevelTime (γ ω) (G ω) x (u n))) ∂volume) ≤ A) :
    (∫⁻ ω, if ENNReal.ofReal (2*H) <
        compactSpatialMass (C.rational.terminal ω) K (closedBall z r) then
      compactSpatialMass (C.rational.terminal ω) K (closedBall z r) else 0 ∂P) ≤ 2*A := by
  have hb := C.bad_cell_mass_le_of_finite_bound hB hc h0 hκ hκ8 F hw
    u hu hmono hlim q hq (K ∩ Subtype.val ⁻¹' closedBall z r)
    (compactSpatialMass_compact_cell K hK z r) H hH A hbound
  simpa only [compactSpatialMass_apply _ _ _ isClosed_closedBall.measurableSet,
    Set.indicator,Set.mem_ofPred_eq] using hb

/-- Finite centered-law bounds imply the prescribed lower-bound criterion.
The gauge and its positive moments are the prescribed nested Wiener coefficients. -/
theorem ae_positive_prescribed_of_finite_tests [IsProbabilityMeasure P]
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (q : ℕ → ℝ≥0) (hq : DenseRange q)
    (K : Set upperHalfPlane) (hK : IsCompact K) (D : ℝ) (hD : 0 < D)
    (p : Target.GaugeIndex κ W → ℝ≥0∞) (hp : (∑' e, p e) ≠ ∞)
    (hbound : ∀ e : Target.GaugeIndex κ W, ∀ i : ℤ×ℤ, ∀ j, ∀ᶠ n in atTop,
      (∫⁻ x in (Subtype.val : upperHalfPlane → ℂ) ''
          (K ∩ Subtype.val ⁻¹' closedBall (coverGridCenter (Target.radii κ W e) i)
            (2*Target.radii κ W e)),
        ENNReal.ofReal (initialGreen κ x) * finiteCenteredLaw P κ B γ G x (u n)
          (finiteStrictPastEvent ((Finset.range j).image q)
            (fun t => {ω | D*Target.weights κ W e*(Target.radii κ W e)^Target.d κ <
              (C.process t ω (K ∩ Subtype.val ⁻¹' closedBall
                (coverGridCenter (Target.radii κ W e) i) (2*Target.radii κ W e))).toReal})
            (fun ω => radiusLevelTime (γ ω) (G ω) x (u n))) ∂volume) ≤
        p e * compactSpatialMass (initialGreenMeasure κ) K
          (closedBall (coverGridCenter (Target.radii κ W e) i) (2*Target.radii κ W e))) :
    ∀ᵐ ω ∂P, ∀ E : Set ℂ, MeasurableSet E →
      0 < C.rational.terminal ω (K ∩ Subtype.val ⁻¹' E) →
      0 < Target.hausdorff (Target.gauge κ W) E := by
  let μ (ω : Ω) := compactSpatialMass (C.rational.terminal ω) K
  let η := compactSpatialMass (initialGreenMeasure κ) K
  let : IsFiniteMeasure η := compact_spatial_initial_finite (κ := κ) K hK
  have hsum : (∑' e : Target.GaugeIndex κ W, 2*p e) ≠ ∞ := by
    rw [ENNReal.tsum_mul_left]
    exact (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hp)).ne
  have hcell (e : Target.GaugeIndex κ W) (i : ℤ×ℤ) :
      (∫⁻ ω, if ENNReal.ofReal
          ((2*D)*Target.weights κ W e*(Target.radii κ W e)^Target.d κ) <
            μ ω (closedBall (coverGridCenter (Target.radii κ W e) i) (2*Target.radii κ W e)) then
          μ ω (closedBall (coverGridCenter (Target.radii κ W e) i) (2*Target.radii κ W e)) else 0 ∂P) ≤
        (2*p e)*η (closedBall (coverGridCenter (Target.radii κ W e) i) (2*Target.radii κ W e)) := by
    have hH : 0 < D*Target.weights κ W e*(Target.radii κ W e)^Target.d κ :=
      mul_pos (mul_pos hD (Target.weights_pos κ W e))
        (Real.rpow_pos_of_pos (Target.radii_pos κ W e) _)
    have hb := C.compact_spatial_bad_charge_of_finite_tests hB hc h0 hκ hκ8 F hw
      u hu hmono hlim q hq K hK (coverGridCenter (Target.radii κ W e) i)
      (2*Target.radii κ W e) _ hH _ (hbound e i)
    have he : (2*D)*Target.weights κ W e*(Target.radii κ W e)^Target.d κ =
        2*(D*Target.weights κ W e*(Target.radii κ W e)^Target.d κ) := by ring
    simpa only [he,mul_assoc] using hb
  have ha := ae_positive_prescribed_hausdorff_of_cell_charges P μ
    (C.compact_spatial_terminal_measurable K hK)
    (C.compact_spatial_terminal_finite K hK) η κ W
    (C.prescribed_gauge_admissible hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW)
    (C.moment_one_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW)
    (fun n _ => C.moment_jensen hB hc h0 hκ hκ8 F hw hgrowth W hW n)
    (2*D) (by positivity) (fun e => 2*p e) hsum (by
      intro e i
      convert hcell e i using 1
      apply lintegral_congr
      intro ω
      split_ifs <;> rfl)
  filter_upwards [ha] with ω hω E hE hpE
  exact hω E hE (by simpa only [μ,compactSpatialMass_apply _ _ _ hE] using hpE)

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
