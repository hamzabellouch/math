import OAI.Probability.SLE.Gauge.ExtendedExperimentStop

namespace OAI

/-! Finite localization of a possibly infinite stopping time. The value
`S.untopD 0` is used only on the event where `S` is finite; it is not asserted
to be a stopping time on the whole sample space. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge

variable {Ω : Type*}

def finiteStopEvent (S : Ω → WithTop ℝ≥0) (n : ℕ) : Set Ω :=
  {ω | S ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}

lemma cutoffStop_le_horizon (S : Ω → WithTop ℝ≥0) (H : ℝ≥0) (ω : Ω) :
    cutoffStop S H ω ≤ H := by
  exact WithTop.coe_le_coe.mp ((cutoffStop_coe S H ω).trans_le (min_le_right _ _))

lemma cutoffStop_le_stop (S : Ω → WithTop ℝ≥0) (H : ℝ≥0) (ω : Ω) :
    (cutoffStop S H ω : WithTop ℝ≥0) ≤ S ω := by
  rw [cutoffStop_coe]
  exact min_le_left _ _

lemma cutoffStop_monotone (S : Ω → WithTop ℝ≥0) (ω : Ω) :
    Monotone (fun H : ℝ≥0 => cutoffStop S H ω) := by
  intro H K hHK
  apply WithTop.coe_le_coe.mp
  rw [cutoffStop_coe,cutoffStop_coe]
  exact min_le_min_left _ (WithTop.coe_le_coe.mpr hHK)

lemma finiteStopEvent_mono (S : Ω → WithTop ℝ≥0) : Monotone (finiteStopEvent S) := by
  intro n k hnk ω hω
  change S ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) at hω
  change S ω ≤ ((k : ℝ≥0) : WithTop ℝ≥0)
  exact hω.trans (WithTop.coe_le_coe.mpr (by exact_mod_cast hnk))

lemma iUnion_finiteStopEvent (S : Ω → WithTop ℝ≥0) :
    (⋃ n, finiteStopEvent S n) = {ω | S ω < ⊤} := by
  ext ω
  simp only [mem_iUnion,finiteStopEvent,mem_ofPred_eq]
  constructor
  · rintro ⟨n,hn⟩
    exact hn.trans_lt (WithTop.coe_lt_top _)
  · intro hω
    lift S ω to ℝ≥0 using hω.ne with t ht
    obtain ⟨n,hn⟩ := exists_nat_ge (t : ℝ)
    refine ⟨n,?_⟩
    exact WithTop.coe_le_coe.mpr (by exact_mod_cast hn)

lemma cutoffStop_eqOn_finiteStopEvent (S : Ω → WithTop ℝ≥0) (n : ℕ) :
    EqOn (cutoffStop S n) (fun ω => (S ω).untopD 0) (finiteStopEvent S n) := by
  intro ω hω
  exact cutoffStop_eq_on_success S n ω hω

lemma cutoffStop_eventually_eq (S : Ω → WithTop ℝ≥0) (ω : Ω) (hω : S ω < ⊤) :
    ∀ᶠ n : ℕ in atTop, cutoffStop S n ω = (S ω).untopD 0 := by
  have hmem : ω ∈ ⋃ n, finiteStopEvent S n := by
    rw [iUnion_finiteStopEvent S]
    exact hω
  obtain ⟨n,hn⟩ := mem_iUnion.mp hmem
  filter_upwards [eventually_ge_atTop n] with k hk
  exact cutoffStop_eqOn_finiteStopEvent S k (finiteStopEvent_mono S hk hn)

section Measurable

variable [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
  (S : Ω → WithTop ℝ≥0) (hS : IsStoppingTime ℱ S)

lemma finiteStopEvent_measurable (n : ℕ) :
    MeasurableSet[hS.measurableSpace] (finiteStopEvent S n) :=
  hS.measurableSet_le' n

lemma finiteStopEvent_measurable_cutoff (n : ℕ) :
    MeasurableSet[(cutoffStop_stopping ℱ S hS n).measurableSpace] (finiteStopEvent S n) := by
  simpa only [Set.univ_inter,finiteStopEvent] using
    cutoffStop_success_measurable ℱ S hS n Set.univ MeasurableSet.univ

lemma finiteStopEvent_inter_measurable_cutoff (n : ℕ) (E : Set Ω)
    (hE : MeasurableSet[hS.measurableSpace] E) :
    MeasurableSet[(cutoffStop_stopping ℱ S hS n).measurableSpace] (E ∩ finiteStopEvent S n) :=
  cutoffStop_success_measurable ℱ S hS n E hE

lemma finiteStopEvent_all_measurable :
    MeasurableSet[hS.measurableSpace] {ω | S ω < ⊤} := by
  rw [← iUnion_finiteStopEvent S]
  exact MeasurableSet.iUnion (finiteStopEvent_measurable ℱ S hS)

lemma cutoffStop_past_le (n : ℕ) :
    (cutoffStop_stopping ℱ S hS n).measurableSpace ≤ hS.measurableSpace :=
  IsStoppingTime.measurableSpace_mono _ hS (cutoffStop_le_stop S n)

lemma ae_of_cutoffStop (P : Measure Ω) (Q : Ω → ℝ≥0 → Prop)
    (hQ : ∀ n : ℕ, ∀ᵐ ω ∂P, Q ω (cutoffStop S n ω)) :
    ∀ᵐ ω ∂P, S ω < ⊤ → Q ω ((S ω).untopD 0) := by
  filter_upwards [ae_all_iff.mpr hQ] with ω hω hfinite
  have hmem : ω ∈ ⋃ n, finiteStopEvent S n := by
    rw [iUnion_finiteStopEvent S]
    exact hfinite
  obtain ⟨n,hn⟩ := mem_iUnion.mp hmem
  simpa only [cutoffStop_eqOn_finiteStopEvent S n hn] using hω n

end Measurable

lemma sourceRestartDriverPath_eq_on_finiteStopEvent
    (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => B t ω))
    (S : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) (hω : ω ∈ finiteStopEvent S n) :
    sourceRestartDriverPath B hc (cutoffStop S n) ω =
      sourceRestartDriverPath B hc (fun ω => (S ω).untopD 0) ω := by
  ext t
  change B (cutoffStop S n ω+t) ω-B (cutoffStop S n ω) ω =
    B ((S ω).untopD 0+t) ω-B ((S ω).untopD 0) ω
  rw [cutoffStop_eqOn_finiteStopEvent S n hω]

end SLEExactGauge

end

end OAI
