import OAI.Probability.SLE.Gauge.ExtendedExperimentStop

namespace OAI

/-! A conditional estimate at finite stopping times extends unchanged to
a stopping time finite almost surely on its admissible stopped-past event.
The geometric state is evaluated only on that event. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem conditional_event_bound_at_extended_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Q : Measure Ω)
    (ℱ : Filtration ℝ≥0 mΩ) (p : ℝ≥0∞) (S : Set Ω)
    (state : Ω → ℝ≥0 → Prop)
    (hfiniteStep : ∀ (τ : Ω → ℝ≥0)
      (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
      (E : Set Ω), MeasurableSet[hτ.measurableSpace] E →
      (∀ ω ∈ E, state ω (τ ω)) → p * Q E ≤ Q (E ∩ S))
    (σ : Ω → WithTop ℝ≥0) (hσ : IsStoppingTime ℱ σ)
    (E : Set Ω) (hE : MeasurableSet[hσ.measurableSpace] E)
    (hfinite : ∀ᵐ ω ∂Q, ω ∈ E → σ ω ≠ ⊤)
    (hstate : ∀ ω ∈ E, state ω ((σ ω).untopD 0)) :
    p * Q E ≤ Q (E ∩ S) := by
  let Eₙ (n : ℕ) := E ∩ {ω | σ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}
  have hmono : Monotone Eₙ := by
    intro n k hnk ω hω
    refine ⟨hω.1, ?_⟩
    change σ ω ≤ ((k : ℝ≥0) : WithTop ℝ≥0)
    exact hω.2.trans (WithTop.coe_le_coe.mpr (by exact_mod_cast hnk))
  have hcover : E =ᵐ[Q] ⋃ n, Eₙ n := by
    filter_upwards [hfinite] with ω hω
    apply propext
    constructor
    · intro hωE
      lift σ ω to ℝ≥0 using hω hωE with t ht
      obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
      exact mem_iUnion.mpr ⟨n, hωE, by
        change σ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)
        rw [← ht]
        exact WithTop.coe_le_coe.mpr (by exact_mod_cast hn)⟩
    · intro hωE
      obtain ⟨n, hn⟩ := mem_iUnion.mp hωE
      exact hn.1
  have hlocal (n : ℕ) : p * Q (Eₙ n) ≤ Q (E ∩ S) := by
    have h := hfiniteStep (cutoffStop σ n) (cutoffStop_stopping ℱ σ hσ n) (Eₙ n)
      (cutoffStop_success_measurable ℱ σ hσ n E hE) (fun ω hω => ?_)
    · exact h.trans (measure_mono (inter_subset_inter inter_subset_left subset_rfl))
    · rw [cutoffStop_eq_on_success σ n ω hω.2]
      exact hstate ω hω.1
  calc
    _ = p * Q (⋃ n, Eₙ n) := by rw [measure_congr hcover]
    _ = ⨆ n, p * Q (Eₙ n) := by rw [hmono.measure_iUnion, ENNReal.mul_iSup]
    _ ≤ _ := iSup_le hlocal

end SLEExactGauge

end

end OAI
