import OAI.Probability.SLE.Gauge.CanonicalGaugeTails
import OAI.Probability.SLE.Geometry.FinitePastTrivialBound

namespace OAI

/-! The lower bound only needs the centered tail comparison in sufficiently
late batches. Every earlier entry is controlled by its finite probability law. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace SLEExactGauge

def prescribedCompactGridCell (κ : ℝ) (W : Target.WienerLaw) (K : Set upperHalfPlane)
    (e : Target.GaugeIndex κ W) (i : ℤ×ℤ) : Set upperHalfPlane :=
  K ∩ Subtype.val ⁻¹' closedBall (coverGridCenter (Target.radii κ W e) i)
    (2*Target.radii κ W e)

namespace Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

theorem ae_positive_prescribed_of_late_disk_tails
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (u : ℕ → ℝ) (hu : ∀ n, 0≤u n) (hmono : Monotone u) (hlim : Tendsto u atTop atTop)
    (q : ℕ → ℝ≥0) (hq : DenseRange q) (K : Set upperHalfPlane) (hK : IsCompact K)
    (D : ℝ) (hD : 0<D) (N : ℕ)
    (hlate : ∀ e : Target.GaugeIndex κ W, N≤e.val.1 → ∀ (i : ℤ×ℤ) (j : ℕ),
      ∀ᶠ n in atTop,
      C.compactFinitePastTest (prescribedCompactGridCell κ W K e i)
        (D*Target.weights κ W e*(Target.radii κ W e)^Target.d κ)
        ((Finset.range j).image q) (u n) ≤
      (2*C.limitingDiskTail hc (16*Target.weights κ W e)) *
        initialGreenMeasure κ (prescribedCompactGridCell κ W K e i)) :
    ∀ᵐ ω ∂P, ∀ E : Set ℂ, MeasurableSet E →
      0 < C.rational.terminal ω (K ∩ Subtype.val ⁻¹' E) →
      0 < Target.hausdorff (Target.gauge κ W) E := by
  let p : Target.GaugeIndex κ W → ℝ≥0∞ := fun e =>
    if e.val.1<N then 1 else 2*C.limitingDiskTail hc (16*Target.weights κ W e)
  have hE : Set.Finite {e : Target.GaugeIndex κ W | e.val.1<N} := by
    apply ((Target.early_entries_finite κ W
      (C.moment_one_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW)
      (fun n _ => C.moment_jensen hB hc h0 hκ hκ8 F hw hgrowth W hW n) N).preimage
      (f := fun e : Target.GaugeIndex κ W => e.val) Subtype.val_injective.injOn).subset
    intro e he
    exact ⟨e.property,he⟩
  have hsE : (∑' e : Target.GaugeIndex κ W, if e.val.1<N then (1:ℝ≥0∞) else 0) ≠ ∞ := by
    rw [tsum_eq_sum (s := hE.toFinset)]
    · apply ne_of_lt
      apply ENNReal.sum_lt_top.mpr
      intro e he
      split_ifs <;> norm_num
    · intro e he
      exact ite_eq_right (by simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using he)
  have hsTail : (∑' e : Target.GaugeIndex κ W,
      2*C.limitingDiskTail hc (16*Target.weights κ W e)) ≠ ∞ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (by norm_num)
      (C.limitingDiskTail_summable hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW)
  have hp : (∑' e, p e) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum (fun e =>
      show p e ≤ (if e.val.1<N then (1:ℝ≥0∞) else 0) +
        2*C.limitingDiskTail hc (16*Target.weights κ W e) by
          dsimp only [p]; split_ifs <;> simp))
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hsE,hsTail⟩
  apply C.ae_positive_prescribed_of_finite_tests hB hc h0 hκ hκ8 F hw hpublished hgrowth
    W hW u hu hmono hlim q hq K hK D hD p hp
  intro e i j
  rw [compactSpatialMass_apply _ _ _ isClosed_closedBall.measurableSet]
  change ∀ᶠ n in atTop, C.compactFinitePastTest (prescribedCompactGridCell κ W K e i)
    (D*Target.weights κ W e*(Target.radii κ W e)^Target.d κ)
    ((Finset.range j).image q) (u n) ≤ p e *
      initialGreenMeasure κ (prescribedCompactGridCell κ W K e i)
  by_cases he : e.val.1<N
  · apply Eventually.of_forall
    intro n
    have hcell : IsCompact (prescribedCompactGridCell κ W K e i) :=
      compactSpatialMass_compact_cell K hK _ _
    simpa only [p,he,ite_true,one_mul] using
      C.compactFinitePastTest_le_initial hB hκ hκ8 F hw
        (prescribedCompactGridCell κ W K e i) hcell _ ((Finset.range j).image q) (u n) (hu n)
  · simpa only [p,he,ite_false] using hlate e (le_of_not_gt he) i j

end Multipoint.CanonicalMass
end SLEExactGauge

end

end OAI
