import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology

namespace CylinderCovering.OpenBaseThickening

variable {E : Type*} [MetricSpace E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [ProperSpace E]

theorem tendsto_real_thickening (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) :
    Tendsto (fun r : ℝ => μ.real (thickening r K)) (𝓝[>] 0) (𝓝 (μ.real K)) := by
  apply (ENNReal.tendsto_toReal hK.measure_lt_top.ne).comp
  exact tendsto_measure_thickening_of_isClosed
    ⟨1, zero_lt_one, hK.isBounded.thickening.measure_lt_top.ne⟩ hK.isClosed

theorem exists_open_enlargement (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set E, K ⊆ U ∧ IsOpen U ∧ Bornology.IsBounded U ∧
      MeasurableSet U ∧ μ.real U < μ.real K + ε := by
  have hlim := tendsto_real_thickening μ hK
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      μ.real (thickening r K) < μ.real K + ε :=
    hlim.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hε))
  obtain ⟨r, hr, harea⟩ := (Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ Ioi (0 : ℝ)) hevent).exists
  refine ⟨thickening r K, self_subset_thickening hr K, isOpen_thickening,
    hK.isBounded.thickening, isOpen_thickening.measurableSet, harea⟩

section FiniteFamily

variable {ι : Type*} [Fintype ι] {F : ι → Type*}
  [∀ i, MetricSpace (F i)] [∀ i, MeasurableSpace (F i)]
  [∀ i, OpensMeasurableSpace (F i)] [∀ i, ProperSpace (F i)]

theorem exists_common_thickening_two_budgets
    (μ : (i : ι) → Measure (F i)) [∀ i, IsFiniteMeasureOnCompacts (μ i)]
    (K : (i : ι) → Set (F i)) (hK : ∀ i, IsCompact (K i))
    (w : ι → ℝ) {A B : ℝ}
    (hA : (∑ i, (μ i).real (K i)) < A)
    (hB : (∑ i, w i * (μ i).real (K i)) < B) :
    ∃ r : ℝ, 0 < r ∧
      (∑ i, (μ i).real (thickening r (K i))) < A ∧
      (∑ i, w i * (μ i).real (thickening r (K i))) < B := by
  have hlimA : Tendsto (fun r : ℝ => ∑ i, (μ i).real (thickening r (K i)))
      (𝓝[>] 0) (𝓝 (∑ i, (μ i).real (K i))) := by
    exact tendsto_finsetSum _ (fun i _ => tendsto_real_thickening (μ i) (hK i))
  have hlimB : Tendsto (fun r : ℝ => ∑ i, w i * (μ i).real (thickening r (K i)))
      (𝓝[>] 0) (𝓝 (∑ i, w i * (μ i).real (K i))) := by
    exact tendsto_finsetSum _ (fun i _ =>
      tendsto_const_nhds.mul (tendsto_real_thickening (μ i) (hK i)))
  have heventA := hlimA.eventually (eventually_lt_nhds hA)
  have heventB := hlimB.eventually (eventually_lt_nhds hB)
  obtain ⟨r, hr, hrA, hrB⟩ :=
    (Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ Ioi (0 : ℝ))
      (heventA.and heventB)).exists
  exact ⟨r, hr, hrA, hrB⟩

theorem exists_open_family_two_budgets
    (μ : (i : ι) → Measure (F i)) [∀ i, IsFiniteMeasureOnCompacts (μ i)]
    (K : (i : ι) → Set (F i)) (hK : ∀ i, IsCompact (K i))
    (w : ι → ℝ) {A B : ℝ}
    (hA : (∑ i, (μ i).real (K i)) < A)
    (hB : (∑ i, w i * (μ i).real (K i)) < B) :
    ∃ U : (i : ι) → Set (F i),
      (∀ i, K i ⊆ U i ∧ IsOpen (U i) ∧ Bornology.IsBounded (U i) ∧
        MeasurableSet (U i)) ∧
      (∑ i, (μ i).real (U i)) < A ∧
      (∑ i, w i * (μ i).real (U i)) < B := by
  obtain ⟨r, hr, harea, hweighted⟩ :=
    exists_common_thickening_two_budgets μ K hK w hA hB
  refine ⟨fun i => thickening r (K i), ?_, harea, hweighted⟩
  intro i
  exact ⟨self_subset_thickening hr (K i), isOpen_thickening,
    (hK i).isBounded.thickening, isOpen_thickening.measurableSet⟩

end FiniteFamily

end CylinderCovering.OpenBaseThickening

end

end OAI
