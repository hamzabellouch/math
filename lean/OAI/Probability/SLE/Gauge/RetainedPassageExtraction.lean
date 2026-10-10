import OAI.Probability.SLE.Gauge.RibbonPassageMass
import OAI.Probability.SLE.Gauge.ConformalCompactSausage

namespace OAI

/-! Countable-to-finite retention in the ribbon passage argument. The loss
is bounded for every varying early-containment event by the same discarded
set. Sausage exceptions are subtracted unconditionally. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

theorem finite_retention_of_countable_cover
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (E : Set Ω) (D : ℕ → Set Ω)
    (hE : MeasurableSet E) (hD : ∀ i, MeasurableSet (D i))
    (hcover : P (E \ ⋃ i, D i) = 0)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ N : ℕ, P (E \ ⋃ i ∈ Finset.range N, D i) < ε := by
  let S : ℕ → Set Ω := fun n => E \ ⋃ i ∈ Finset.range n, D i
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    hE.diff ((Finset.range n).measurableSet_biUnion (fun i _ => hD i))
  have hSa : Antitone S := by
    intro n k hnk ω hω
    refine ⟨hω.1, ?_⟩
    intro hn
    obtain ⟨i, hi, hDi⟩ := mem_iUnion₂.mp hn
    exact hω.2 (mem_iUnion₂.mpr ⟨i, Finset.range_mono hnk hi, hDi⟩)
  have hi : ⋂ n, S n = E \ ⋃ i, D i := by
    ext ω
    constructor
    · intro h
      refine ⟨(mem_iInter.mp h 0).1, ?_⟩
      intro hω
      obtain ⟨i, hi⟩ := mem_iUnion.mp hω
      exact (mem_iInter.mp h (i + 1)).2
        (mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_self i), hi⟩)
    · rintro ⟨hEω, hω⟩
      apply mem_iInter.mpr
      intro n
      refine ⟨hEω, ?_⟩
      intro hn
      obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hn
      exact hω (mem_iUnion.mpr ⟨i, hi⟩)
  have ht : Tendsto (fun n => P (S n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hi, hcover] using
      tendsto_measure_iInter_atTop (fun n => (hSm n).nullMeasurableSet)
        hSa ⟨0, measure_ne_top P _⟩
  exact (ht.eventually (gt_mem_nhds hε)).exists

/-- Discarding one small set preserves a fixed fraction of every member
of a varying family; no independence is involved. -/
theorem varying_events_after_finite_retention
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (E : Set Ω) (D : ℕ → Set Ω) (G : ℕ → Set Ω)
    (hE : MeasurableSet E) (hD : ∀ i, MeasurableSet (D i))
    (hcover : P (E \ ⋃ i, D i) = 0)
    (q : ℝ) (hq : 0 < q)
    (hG : ∀ n, ENNReal.ofReal q ≤ P (G n ∩ E)) :
    ∃ N : ℕ, ∀ n, ENNReal.ofReal (q / 2) ≤
      P (G n ∩ E ∩ ⋃ i ∈ Finset.range N, D i) := by
  obtain ⟨N, hN⟩ := finite_retention_of_countable_cover P E D hE hD hcover
    (ENNReal.ofReal (q / 2)) (ENNReal.ofReal_pos.mpr (by positivity))
  refine ⟨N, fun n => ?_⟩
  let R := ⋃ i ∈ Finset.range N, D i
  have hsub : G n ∩ E ⊆ (G n ∩ E ∩ R) ∪ (E \ R) := by
    intro ω hω
    by_cases hR : ω ∈ R
    · exact Or.inl ⟨hω, hR⟩
    · exact Or.inr ⟨hω.2, hR⟩
  have hbound : ENNReal.ofReal q ≤ P (G n ∩ E ∩ R) + P (E \ R) :=
    (hG n).trans ((measure_mono hsub).trans (measure_union_le _ _))
  by_contra h
  have hhalf : ENNReal.ofReal (q / 2) + ENNReal.ofReal (q / 2) =
      ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  exact (not_lt_of_ge hbound) (hhalf ▸ ENNReal.add_lt_add (lt_of_not_ge h) hN)

end SLEExactGauge

end

end OAI
