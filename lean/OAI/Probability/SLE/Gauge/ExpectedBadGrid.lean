import OAI.Probability.SLE.Gauge.RandomBadGrid
import OAI.Probability.SLE.Mass.GridMassOverlap

namespace OAI

/-! Individual cell charge estimates combine with fixed grid overlap and
summable prescribed tails to give the complete lower-bound criterion. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma expected_badGrid_mass_le_overlap
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : Measurable μ) (η : Measure ℂ)
    (r : ℝ) (hr : 0 < r) (H : ℝ) (p : ℝ≥0∞)
    (hcell : ∀ i : ℤ×ℤ,
      (∫⁻ ω, if ENNReal.ofReal H < μ ω (closedBall (coverGridCenter r i) (2*r)) then
        μ ω (closedBall (coverGridCenter r i) (2*r)) else 0 ∂P) ≤
      p*η (closedBall (coverGridCenter r i) (2*r))) :
    (∫⁻ ω, μ ω (badGridCells (μ ω) r H) ∂P) ≤ 81*p*η univ := by
  calc
    _ ≤ ∑' i : ℤ×ℤ,
        ∫⁻ ω, if ENNReal.ofReal H < μ ω (closedBall (coverGridCenter r i) (2*r)) then
          μ ω (closedBall (coverGridCenter r i) (2*r)) else 0 ∂P :=
      expected_badGrid_mass_le_sum P μ hμ r H
    _ ≤ ∑' i : ℤ×ℤ, p*η (closedBall (coverGridCenter r i) (2*r)) := ENNReal.tsum_le_tsum hcell
    _ = p*(∑' i : ℤ×ℤ, η (closedBall (coverGridCenter r i) (2*r))) := ENNReal.tsum_mul_left
    _ ≤ p*(81*η univ) := mul_le_mul' le_rfl (grid_mass_sum_le η hr)
    _ = _ := by ac_rfl

lemma ae_positive_prescribed_hausdorff_of_cell_charges
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : Measurable μ) (hfin : ∀ ω, IsFiniteMeasure (μ ω))
    (η : Measure ℂ) [IsFiniteMeasure η] (κ : ℝ) (W : Target.WienerLaw)
    (hg : Target.IsHausdorffGauge (Target.gauge κ W))
    (hm1 : 0 < Target.moment κ W 1)
    (hJ : ∀ n : ℕ, 1 ≤ n → Target.moment κ W 1^n ≤ Target.moment κ W n)
    (D : ℝ) (hD : 0 ≤ D) (p : Target.GaugeIndex κ W → ℝ≥0∞)
    (hp : (∑' e, p e) ≠ ∞)
    (hcell : ∀ e : Target.GaugeIndex κ W, ∀ i : ℤ×ℤ,
      (∫⁻ ω, if ENNReal.ofReal
          (D*Target.weights κ W e*(Target.radii κ W e)^Target.d κ) <
            μ ω (closedBall (coverGridCenter (Target.radii κ W e) i) (2*Target.radii κ W e)) then
          μ ω (closedBall (coverGridCenter (Target.radii κ W e) i) (2*Target.radii κ W e)) else 0 ∂P) ≤
        p e*η (closedBall (coverGridCenter (Target.radii κ W e) i) (2*Target.radii κ W e))) :
    ∀ᵐ ω ∂P, ∀ E : Set ℂ, MeasurableSet E → 0 < μ ω E →
      0 < Target.hausdorff (Target.gauge κ W) E := by
  apply ae_positive_prescribed_hausdorff_of_bad_mass P μ hμ hfin κ W hg hm1 hJ D hD
  have hb : (∑' e : Target.GaugeIndex κ W,
      ∫⁻ ω, μ ω (prescribedBadGrid (μ ω) κ W D e) ∂P) ≤
      81*(∑' e, p e)*η univ := by
    calc
      _ ≤ ∑' e : Target.GaugeIndex κ W, 81*p e*η univ := ENNReal.tsum_le_tsum
        (fun e => expected_badGrid_mass_le_overlap P μ hμ η _ (Target.radii_pos κ W e) _ (p e) (hcell e))
      _ = _ := by rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]
  exact ne_top_of_le_ne_top
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hp))
      (measure_lt_top η univ)).ne hb

end SLEExactGauge

end

end OAI
