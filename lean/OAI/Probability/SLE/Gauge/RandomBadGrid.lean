import OAI.Probability.SLE.Gauge.GoodGridRestriction

namespace OAI

/-! Measurability and almost-sure finiteness of the bad-grid mass sum.
Only expectations of the actual cell masses occur in the criterion. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma measurableSet_random_badGridCells
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    (r H : ℝ) : MeasurableSet {p : Ω × ℂ | p.2 ∈ badGridCells (μ p.1) r H} := by
  classical
  let Q := fun i : ℤ × ℤ => closedBall (coverGridCenter r i) (2*r)
  have he : {p : Ω × ℂ | p.2 ∈ badGridCells (μ p.1) r H} =
      ⋃ i : ℤ × ℤ, {ω | ENNReal.ofReal H < μ ω (Q i)} ×ˢ Q i := by
    ext p
    constructor
    · intro hp
      obtain ⟨i,hi⟩ := mem_iUnion.mp hp
      change p.2 ∈ if ENNReal.ofReal H < μ p.1 (Q i) then Q i else ∅ at hi
      by_cases h : ENNReal.ofReal H < μ p.1 (Q i)
      · rw [ite_eq_left h] at hi
        exact mem_iUnion.mpr ⟨i,h,hi⟩
      · rw [ite_eq_right h] at hi
        exact hi.elim
    · intro hp
      obtain ⟨i,hi⟩ := mem_iUnion.mp hp
      apply mem_iUnion.mpr
      refine ⟨i,?_⟩
      change p.2 ∈ if ENNReal.ofReal H < μ p.1 (Q i) then Q i else ∅
      rw [ite_eq_left (show ENNReal.ofReal H < μ p.1 (Q i) from hi.1)]
      exact hi.2
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  exact (measurableSet_lt measurable_const
    ((Measure.measurable_coe measurableSet_closedBall).comp hμ)).prod measurableSet_closedBall

lemma random_badGrid_mass_measurable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasure (μ ω)) (r H : ℝ) :
    Measurable (fun ω => μ ω (badGridCells (μ ω) r H)) := by
  let K : Kernel Ω ℂ := ⟨μ,hμ⟩
  exact Kernel.measurable_kernel_prodMk_left_of_finite (κ:=K)
    (measurableSet_random_badGridCells μ hμ r H) hfin

lemma badGrid_mass_le_sum (μ : Measure ℂ) (r H : ℝ) :
    μ (badGridCells μ r H) ≤ ∑' i : ℤ × ℤ,
      if ENNReal.ofReal H < μ (closedBall (coverGridCenter r i) (2*r)) then
        μ (closedBall (coverGridCenter r i) (2*r)) else 0 := by
  classical
  calc
    _ ≤ ∑' i : ℤ × ℤ, μ (if ENNReal.ofReal H < μ (closedBall (coverGridCenter r i) (2*r)) then
      closedBall (coverGridCenter r i) (2*r) else ∅) := measure_iUnion_le _
    _ = _ := by
      apply tsum_congr
      intro i
      split_ifs <;> simp

lemma expected_badGrid_mass_le_sum
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : Measurable μ) (r H : ℝ) :
    (∫⁻ ω, μ ω (badGridCells (μ ω) r H) ∂P) ≤ ∑' i : ℤ × ℤ,
      ∫⁻ ω, if ENNReal.ofReal H < μ ω (closedBall (coverGridCenter r i) (2*r)) then
        μ ω (closedBall (coverGridCenter r i) (2*r)) else 0 ∂P := by
  classical
  calc
    _ ≤ ∫⁻ ω, ∑' i : ℤ × ℤ,
        if ENNReal.ofReal H < μ ω (closedBall (coverGridCenter r i) (2*r)) then
          μ ω (closedBall (coverGridCenter r i) (2*r)) else 0 ∂P :=
      lintegral_mono (fun ω => badGrid_mass_le_sum (μ ω) r H)
    _ = _ := by
      apply lintegral_tsum
      intro i
      exact (Measurable.ite (measurableSet_lt measurable_const
        ((Measure.measurable_coe measurableSet_closedBall).comp hμ))
        ((Measure.measurable_coe measurableSet_closedBall).comp hμ) measurable_const).aemeasurable

lemma ae_prescribedBadGrid_sum_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : Measurable μ) (hfin : ∀ ω, IsFiniteMeasure (μ ω))
    (κ : ℝ) (W : Target.WienerLaw) (D : ℝ)
    (hsum : (∑' e : Target.GaugeIndex κ W,
      ∫⁻ ω, μ ω (prescribedBadGrid (μ ω) κ W D e) ∂P) ≠ ∞) :
    ∀ᵐ ω ∂P, (∑' e : Target.GaugeIndex κ W, μ ω (prescribedBadGrid (μ ω) κ W D e)) ≠ ∞ := by
  have hm (e : Target.GaugeIndex κ W) :
      Measurable (fun ω => μ ω (prescribedBadGrid (μ ω) κ W D e)) :=
    random_badGrid_mass_measurable μ hμ hfin _ _
  have hi : (∫⁻ ω, ∑' e : Target.GaugeIndex κ W,
      μ ω (prescribedBadGrid (μ ω) κ W D e) ∂P) ≠ ∞ := by
    rw [lintegral_tsum (fun e => (hm e).aemeasurable)]
    exact hsum
  exact (ae_lt_top (Measurable.tsum hm) hi).mono (fun _ h => h.ne)

lemma ae_positive_prescribed_hausdorff_of_bad_mass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : Measurable μ) (hfin : ∀ ω, IsFiniteMeasure (μ ω))
    (κ : ℝ) (W : Target.WienerLaw)
    (hg : Target.IsHausdorffGauge (Target.gauge κ W))
    (hm1 : 0 < Target.moment κ W 1)
    (hJ : ∀ n : ℕ, 1 ≤ n → Target.moment κ W 1^n ≤ Target.moment κ W n)
    (D : ℝ) (hD : 0 ≤ D)
    (hsum : (∑' e : Target.GaugeIndex κ W,
      ∫⁻ ω, μ ω (prescribedBadGrid (μ ω) κ W D e) ∂P) ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ E : Set ℂ, MeasurableSet E → 0 < μ ω E →
      0 < Target.hausdorff (Target.gauge κ W) E := by
  filter_upwards [ae_prescribedBadGrid_sum_finite P μ hμ hfin κ W D hsum] with ω hω
  let := hfin ω
  exact fun E hE hp => positive_prescribed_hausdorff_of_summable_bad_mass
    (μ ω) κ W hg hm1 hJ D hD hω E hE hp

end SLEExactGauge

end

end OAI
