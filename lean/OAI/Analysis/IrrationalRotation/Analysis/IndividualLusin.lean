import Mathlib

namespace OAI

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace Invariant233.Lusin

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [T2Space X] [CompactSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]

theorem exists_compact_clopen_restrictions (A : ℕ → Set X)
    (hA : ∀ n, MeasurableSet (A n)) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧
      ∀ n, ∃ U : Set X, IsOpen U ∧ A n ∩ K = U ∩ K := by
  classical
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε (ℕ × Bool)
  let E : ℕ × Bool → Set X := fun p => if p.2 then A p.1 else (A p.1)ᶜ
  have hE : ∀ p, MeasurableSet (E p) := by
    rintro ⟨n, b⟩
    cases b <;> simp only [E, Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hA n | exact (hA n).compl
  have happrox : ∀ p : ℕ × Bool, ∃ C : Set X,
      C ⊆ E p ∧ IsCompact C ∧ μ (E p \ C) < δ p := by
    intro p
    exact (hE p).exists_isCompact_sdiff_lt (measure_ne_top μ (E p)) (hδpos p).ne'
  choose C hCsub hCcompact hCmeasure using happrox
  let K : Set X := ⋂ n : ℕ, C (n, true) ∪ C (n, false)
  have hKclosed : IsClosed K :=
    isClosed_iInter fun n => (hCcompact (n, true)).isClosed.union (hCcompact (n, false)).isClosed
  have hKmem : ∀ {x : X}, x ∈ K → ∀ n, x ∈ C (n, true) ∪ C (n, false) := by
    intro x hx n
    exact mem_iInter.mp hx n
  have hbad : Kᶜ ⊆ ⋃ p : ℕ × Bool, E p \ C p := by
    intro x hx
    have hn : ∃ n : ℕ, x ∉ C (n, true) ∪ C (n, false) := by
      simpa only [K, mem_compl_iff, mem_iInter, not_forall] using hx
    obtain ⟨n, hn⟩ := hn
    by_cases ha : x ∈ A n
    · apply mem_iUnion.mpr
      refine ⟨(n, true), ?_, ?_⟩
      · simpa [E] using ha
      · exact fun hc => hn (Or.inl hc)
    · apply mem_iUnion.mpr
      refine ⟨(n, false), ?_, ?_⟩
      · simpa [E] using ha
      · exact fun hc => hn (Or.inr hc)
  refine ⟨K, hKclosed.isCompact, ?_, ?_⟩
  · calc
      μ Kᶜ ≤ μ (⋃ p : ℕ × Bool, E p \ C p) := measure_mono hbad
      _ ≤ ∑' p : ℕ × Bool, μ (E p \ C p) := measure_iUnion_le _
      _ ≤ ∑' p : ℕ × Bool, δ p := ENNReal.tsum_le_tsum fun p => (hCmeasure p).le
      _ < ε := hδsum
  · intro n
    refine ⟨(C (n, false))ᶜ, (hCcompact (n, false)).isClosed.isOpen_compl, ?_⟩
    ext x
    constructor
    · rintro ⟨ha, hk⟩
      refine ⟨?_, hk⟩
      intro hc
      have : x ∈ (A n)ᶜ := by simpa [E] using hCsub (n, false) hc
      exact this ha
    · rintro ⟨hc, hk⟩
      refine ⟨?_, hk⟩
      rcases hKmem hk n with ht | hf
      · simpa [E] using hCsub (n, true) ht
      · exact False.elim (hc hf)

theorem exists_compact_continuousOn {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    {f : X → Y} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  obtain ⟨B, hB⟩ := TopologicalSpace.exists_seq_basis Y
  have hA : ∀ n : ℕ, MeasurableSet (f ⁻¹' B n) := by
    intro n
    exact hf (hB.isOpen (mem_range_self n)).measurableSet
  obtain ⟨K, hK, hμK, hrestr⟩ :=
    exists_compact_clopen_restrictions μ (fun n => f ⁻¹' B n) hA hε
  refine ⟨K, hK, hμK, hB.continuousOn_iff.mpr ?_⟩
  intro U hU
  obtain ⟨n, rfl⟩ := hU
  exact hrestr n

end Invariant233.Lusin

end OAI
