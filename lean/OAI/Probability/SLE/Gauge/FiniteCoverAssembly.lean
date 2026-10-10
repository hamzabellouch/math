import OAI.Probability.SLE.Gauge.DenseCoverCore
import OAI.Probability.SLE.Gauge.ExpectedCoverCharge

namespace OAI

/-! Finite selected/missed covers and measurable envelopes for their costs. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

/-- The one-mesh charge is a measure, so disjoint candidates can be summed. -/
def wholeSausageMeasure (κ : ℝ) (γ : ℝ≥0 → ℂ) (v : ℝ) : Measure ℂ :=
  ENNReal.ofReal (v ^ (-codimension κ)) • volume.restrict (wholeSausageSet γ v)

lemma wholeSausageMeasure_apply (κ : ℝ) (γ : ℝ≥0 → ℂ) (v : ℝ)
    {A : Set ℂ} (hA : MeasurableSet A) :
    wholeSausageMeasure κ γ v A = wholeSausageCharge κ γ v A := by
  simp [wholeSausageMeasure, wholeSausageCharge, Measure.restrict_apply hA]

/-- Pointwise existence of finite covers suffices. Their selection need not be
measurable when a measurable envelope controls their costs. -/
theorem hausdorff_le_liminf_finite_cover_envelope
    (h : ℝ → ℝ) (E : Set ℂ) (δ : ℕ → ℝ≥0∞)
    (hδ : Tendsto δ atTop (𝓝 0)) (Z : ℕ → ℝ≥0∞)
    (hcovers : ∀ n, ∃ (N : ℕ) (U : Fin N → Set ℂ),
      E ⊆ ⋃ j, U j ∧ (∀ j, ediam (U j) ≤ δ n) ∧
        ∑ j, extendedGauge h (ediam (U j)) ≤ Z n) :
    hausdorffGauge h E ≤ liminf Z atTop := by
  choose N U hc hd hz using hcovers
  exact (Measure.mkMetric_le_liminf_sum E δ hδ U
    (Eventually.of_forall hd) (Eventually.of_forall hc) (extendedGauge h)).trans
      (liminf_le_liminf (Eventually.of_forall hz))

/-- Fatou applied to the cost envelope, rather than to a chosen random cover. -/
theorem expected_hausdorff_le_of_finite_cover_envelopes
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : ℝ → ℝ) (E : Ω → Set ℂ) (δ : ℕ → ℝ≥0∞)
    (hδ : Tendsto δ atTop (𝓝 0)) (Z : ℕ → Ω → ℝ≥0∞)
    (hZ : ∀ n, AEMeasurable (Z n) P)
    (hcovers : ∀ᵐ ω ∂P, ∀ n, ∃ (N : ℕ) (U : Fin N → Set ℂ),
      E ω ⊆ ⋃ j, U j ∧ (∀ j, ediam (U j) ≤ δ n) ∧
        ∑ j, extendedGauge h (ediam (U j)) ≤ Z n ω)
    (C : ℝ≥0∞) (hcost : liminf (fun n => ∫⁻ ω, Z n ω ∂P) atTop ≤ C) :
    (∫⁻ ω, hausdorffGauge h (E ω) ∂P) ≤ C := by
  calc
    _ ≤ ∫⁻ ω, liminf (fun n => Z n ω) atTop ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hcovers] with ω hc
      exact hausdorff_le_liminf_finite_cover_envelope h (E ω) δ hδ
        (fun n => Z n ω) hc
    _ ≤ liminf (fun n => ∫⁻ ω, Z n ω ∂P) atTop := lintegral_liminf_le' hZ
    _ ≤ C := hcost

/-- Disjoint candidate disks and all missed cells give a genuine finite cover
with cost paid by one spatial measure and the missed-cell sum. -/
theorem exists_finite_selected_missed_cover
    {ι η : Type*} (I : Finset ι) (M : Finset η)
    (x : ι → ℂ) (r : ι → ℝ) (Q : η → Set ℂ)
    (E A : Set ℂ) (ν : Measure ℂ) (h : ℝ → ℝ)
    (R : ℝ) (hr : ∀ i ∈ I, r i ≤ R) (δ C : ℝ≥0∞)
    (hA : ∀ i ∈ I, closedBall (x i) (r i) ⊆ A)
    (hcost : ∀ i ∈ I,
      extendedGauge h (ediam (closedBall (x i) (4 * r i))) ≤
        C * ν (closedBall (x i) (r i)))
    (hdisk : ∀ i ∈ I, ediam (closedBall (x i) (4 * r i)) ≤ δ)
    (hmiss : ∀ k ∈ M, ediam (Q k) ≤ δ)
    (hcell : ∀ z ∈ E, (∃ i ∈ I, z ∈ closedBall (x i) (r i)) ∨
      ∃ k ∈ M, z ∈ Q k) :
    ∃ (N : ℕ) (U : Fin N → Set ℂ), E ⊆ ⋃ j, U j ∧
      (∀ j, ediam (U j) ≤ δ) ∧
      ∑ j, extendedGauge h (ediam (U j)) ≤
        C * ν A + ∑ k ∈ M, extendedGauge h (ediam (Q k)) := by
  classical
  obtain ⟨J, hJI, _, hselect, hcharge⟩ :=
    select_disjoint_candidates_and_charge I x r R hr ν A hA
      (fun i => extendedGauge h (ediam (closedBall (x i) (4 * r i)))) C hcost
  let W : ({i // i ∈ J} ⊕ {k // k ∈ M}) → Set ℂ :=
    Sum.elim (fun i => closedBall (x i) (4 * r i)) (fun k => Q k)
  let e := Fintype.equivFin ({i // i ∈ J} ⊕ {k // k ∈ M})
  refine ⟨_, W ∘ e.symm, ?_, ?_, ?_⟩
  · intro z hz
    rcases selected_and_missed_cover I J M
        (fun i => closedBall (x i) (r i))
        (fun i => closedBall (x i) (4 * r i)) Q E hselect hcell hz with hz | hz
    · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion.mpr ⟨e (Sum.inl ⟨i, hi⟩), by simpa [W] using hzi⟩
    · obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion.mpr ⟨e (Sum.inr ⟨k, hk⟩), by simpa [W] using hzk⟩
  · intro j
    change ediam (W (e.symm j)) ≤ δ
    rcases e.symm j with i | k
    · exact hdisk i (hJI i.property)
    · exact hmiss k k.property
  · calc
      _ = (∑ i ∈ J, extendedGauge h (ediam (closedBall (x i) (4 * r i)))) +
          ∑ k ∈ M, extendedGauge h (ediam (Q k)) := by
        rw [← Equiv.sum_comp e]
        simp only [Function.comp_apply, Equiv.symm_apply_apply, Fintype.sum_sum_type,
          W, Sum.elim_inl, Sum.elim_inr]
        exact congrArg₂ (· + ·)
          (Finset.sum_coe_sort J
            (fun i => extendedGauge h (ediam (closedBall (x i) (4 * r i)))))
          (Finset.sum_coe_sort M (fun k => extendedGauge h (ediam (Q k))))
      _ ≤ _ := add_le_add hcharge le_rfl

/-- The finite cover can be chosen independently at every sample and scale.
Only its common sausage charge and missed-cell envelope need measurability. -/
theorem expected_hausdorff_le_of_finite_sausage_covers
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (h : ℝ → ℝ) (E : Ω → Set ℂ) (δ : ℕ → ℝ≥0∞)
    (hδ : Tendsto δ atTop (𝓝 0))
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (R : ℝ) (C : ℝ≥0)
    (error : ℕ → Ω → ℝ≥0∞) (herr : ∀ n, AEMeasurable (error n) P)
    (herrlim : Tendsto (fun n => ∫⁻ ω, error n ω ∂P) atTop (𝓝 0))
    (hcovers : ∀ᵐ ω ∂P, ∀ n, ∃ (N : ℕ) (U : Fin N → Set ℂ),
      E ω ⊆ ⋃ j, U j ∧ (∀ j, ediam (U j) ≤ δ n) ∧
        ∑ j, extendedGauge h (ediam (U j)) ≤
          (C : ℝ≥0∞) * wholeSausageCharge κ (γ ω) (v n) (closedBall 0 R) + error n ω) :
    (∫⁻ ω, hausdorffGauge h (E ω) ∂P) ≤
      (C : ℝ≥0∞) * wholeSausageChargeBound κ R := by
  obtain ⟨_, hsausage⟩ := source_cover_charge P κ hκ hκ8 γ hSLE R
  let Z (n : ℕ) (ω : Ω) := (C : ℝ≥0∞) *
    wholeSausageCharge κ (γ ω) (v n) (closedBall 0 R) + error n ω
  have hZ (n : ℕ) : AEMeasurable (Z n) P :=
    ((hsausage (v n) (hv n)).1.const_mul _).add (herr n)
  have hcost (n : ℕ) : (∫⁻ ω, Z n ω ∂P) ≤
      (C : ℝ≥0∞) * wholeSausageChargeBound κ R + ∫⁻ ω, error n ω ∂P := by
    dsimp [Z]
    rw [lintegral_add_right' _ (herr n),
      lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    exact add_le_add (mul_le_mul' le_rfl (hsausage (v n) (hv n)).2) le_rfl
  apply expected_hausdorff_le_of_finite_cover_envelopes P h E δ hδ Z hZ hcovers
  have ht : Tendsto (fun n => (C : ℝ≥0∞) * wholeSausageChargeBound κ R +
      ∫⁻ ω, error n ω ∂P) atTop
      (𝓝 ((C : ℝ≥0∞) * wholeSausageChargeBound κ R)) := by
    simpa only [add_zero] using tendsto_const_nhds.add herrlim
  exact (liminf_le_liminf (Eventually.of_forall hcost)).trans_eq ht.liminf_eq

end SLEExactGauge

end

end OAI
