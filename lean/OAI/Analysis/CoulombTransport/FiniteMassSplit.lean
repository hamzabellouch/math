import Mathlib

namespace OAI

universe uAlpha uIndex

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Problem356

/-- The cumulative mass of a finite real measure with null singletons is continuous. -/
theorem continuous_real_cumulative (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] : Continuous (fun t : ℝ => μ.real (Iic t)) := by
  have hc : Continuous (fun t : ℝ => ∫ x in Iic t, (1 : ℝ) ∂μ) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (t + 1)) μ :=
      (integrable_const (1 : ℝ)).integrableOn
    exact hi.continuousOn_Iic_primitive_Iic.continuousAt (Iic_mem_nhds (by linarith))
  simpa using hc

/-- Every strictly intermediate mass is the mass of a lower interval. -/
theorem exists_real_cumulative_eq (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {r : ℝ} (hr : 0 < r) (hrμ : r < μ.real univ) :
    ∃ t : ℝ, μ.real (Iic t) = r := by
  have hbot : Tendsto (fun t : ℝ => μ.real (Iic t)) atBot (𝓝 0) := by
    simpa using (tendsto_integral_Iic_zero (μ := μ) (f := fun _ : ℝ => (1 : ℝ))
      (a := id) tendsto_id)
  have htop : Tendsto (fun t : ℝ => μ.real (Iic t)) atTop (𝓝 (μ.real univ)) := by
    exact (ENNReal.continuousAt_toReal (measure_ne_top μ univ)).tendsto.comp
      (tendsto_measure_Iic_atTop μ)
  exact mem_range_of_exists_le_of_exists_ge (continuous_real_cumulative μ)
    ((hbot.eventually (gt_mem_nhds hr)).exists.imp (fun _ h => h.le))
    ((htop.eventually (lt_mem_nhds hrμ)).exists.imp (fun _ h => h.le))

/-- A finite measure with null singletons on a standard Borel space can realize
any prescribed mass inside any measurable set. -/
theorem exists_measurable_subset_measure_eq {α : Type uAlpha} [MeasurableSpace α]
    [StandardBorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {A : Set α} (hA : MeasurableSet A)
    {r : ℝ≥0∞} (hr : r ≤ μ A) :
    ∃ B : Set α, MeasurableSet B ∧ B ⊆ A ∧ μ B = r := by
  by_cases hzero : r = 0
  · exact ⟨∅, MeasurableSet.empty, empty_subset _, by simp [hzero]⟩
  by_cases hfull : r = μ A
  · exact ⟨A, hA, Subset.rfl, hfull.symm⟩
  obtain ⟨e, he⟩ := exists_measurableEmbedding_real α
  let ν : Measure ℝ := Measure.map e (μ.restrict A)
  have : NullSingletonClass ν := by
    constructor
    intro y
    rw [show ν {y} = (μ.restrict A) (e ⁻¹' {y}) from
      Measure.map_apply he.measurable (measurableSet_singleton y)]
    have hs : (e ⁻¹' {y}).Subsingleton := by
      intro x hx z hz
      exact he.injective (hx.trans hz.symm)
    exact hs.measure_zero (μ.restrict A)
  have hν : ν univ = μ A := by simp [ν, Measure.map_apply, he.measurable]
  have hrfinite : r ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top μ A) hr
  have hpos : 0 < r.toReal := ENNReal.toReal_pos hzero hrfinite
  have hlt : r.toReal < ν.real univ := by
    rw [measureReal_def, hν]
    exact (ENNReal.toReal_lt_toReal hrfinite (measure_ne_top μ A)).2
      (lt_of_le_of_ne hr hfull)
  obtain ⟨t, ht⟩ := exists_real_cumulative_eq ν hpos hlt
  have hmass : ν (Iic t) = r := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν _) hrfinite).1
    exact ht
  refine ⟨e ⁻¹' Iic t ∩ A, (he.measurable measurableSet_Iic).inter hA,
    inter_subset_right, ?_⟩
  simpa [ν, Measure.map_apply he.measurable measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply
      (he.measurable measurableSet_Iic)] using hmass

/-- Finitely many prescribed masses whose total does not exceed the mass of a
measurable set can be realized by pairwise disjoint measurable subsets. -/
theorem exists_fin_disjoint_subsets_measure {α : Type uAlpha} [MeasurableSpace α]
    [StandardBorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {n : ℕ} (q : Fin n → ℝ≥0∞)
    {A : Set α} (hA : MeasurableSet A) (hq : ∑ i, q i ≤ μ A) :
    ∃ B : Fin n → Set α,
      (∀ i, MeasurableSet (B i)) ∧ (∀ i, B i ⊆ A) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧ (∀ i, μ (B i) = q i) := by
  classical
  induction n generalizing A with
  | zero =>
      exact ⟨Fin.elim0, by simp, by simp, by simp [Pairwise], by simp⟩
  | succ n ih =>
      have hq0 : q 0 ≤ μ A := by
        exact (Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ 0)).trans hq
      obtain ⟨B0, hm0, hs0, hmass0⟩ := exists_measurable_subset_measure_eq μ hA hq0
      have htail : ∑ i : Fin n, q i.succ ≤ μ (A \ B0) := by
        rw [measure_sdiff hs0 hm0.nullMeasurableSet (measure_ne_top μ B0), hmass0]
        apply ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top (measure_ne_top μ A) hq0)
        simpa [Fin.sum_univ_succ] using hq
      obtain ⟨B, hm, hs, hd, hmass⟩ := ih (fun i => q i.succ) (hA.diff hm0) htail
      refine ⟨Fin.cons B0 B, ?_, ?_, ?_, ?_⟩
      · intro i
        exact Fin.cases hm0 hm i
      · intro i
        exact Fin.cases hs0 (fun i => (hs i).trans sdiff_subset) i
      · intro i j hij
        cases i using Fin.cases <;> cases j using Fin.cases
        · exact (hij rfl).elim
        · simpa using (disjoint_sdiff_right.mono_right (hs _))
        · simpa using (disjoint_sdiff_right.mono_right (hs _)).symm
        · exact hd (fun h => hij (congrArg Fin.succ h))
      · intro i
        exact Fin.cases hmass0 hmass i

/-- Fintype-indexed version of finite prescribed-mass splitting. -/
theorem exists_finite_disjoint_subsets_measure {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]
    [StandardBorelSpace α] [Fintype ι] (μ : Measure α) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (q : ι → ℝ≥0∞)
    {A : Set α} (hA : MeasurableSet A) (hq : ∑ i, q i ≤ μ A) :
    ∃ B : ι → Set α,
      (∀ i, MeasurableSet (B i)) ∧ (∀ i, B i ⊆ A) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧ (∀ i, μ (B i) = q i) := by
  classical
  let e := Fintype.equivFin ι
  have hsum : ∑ i, q (e.symm i) ≤ μ A := by
    simpa only [e.symm.sum_comp] using hq
  obtain ⟨B, hm, hs, hd, hmass⟩ :=
    exists_fin_disjoint_subsets_measure μ (fun i => q (e.symm i)) hA hsum
  refine ⟨fun i => B (e i), fun i => hm (e i), fun i => hs (e i), ?_, ?_⟩
  · intro i j hij
    exact hd (fun h => hij (e.injective h))
  · intro i
    simpa using hmass (e i)

/-- When prescribed masses exhaust the source mass, the disjoint subsets cover
it up to a null remainder. Empty index types are allowed. -/
theorem exists_finite_mass_partition_ae {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]
    [StandardBorelSpace α] [Fintype ι] (μ : Measure α) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (q : ι → ℝ≥0∞)
    {A : Set α} (hA : MeasurableSet A) (hq : ∑ i, q i = μ A) :
    ∃ B : ι → Set α,
      (∀ i, MeasurableSet (B i)) ∧ (∀ i, B i ⊆ A) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ i, μ (B i) = q i) ∧ μ (A \ ⋃ i, B i) = 0 := by
  obtain ⟨B, hm, hs, hd, hmass⟩ := exists_finite_disjoint_subsets_measure μ q hA hq.le
  refine ⟨B, hm, hs, hd, hmass, ?_⟩
  have hmass_union : μ (⋃ i, B i) = μ A := by
    rw [measure_iUnion hd hm, tsum_fintype]
    simpa only [hmass] using hq
  rw [measure_sdiff (iUnion_subset hs) (MeasurableSet.iUnion hm).nullMeasurableSet
    (measure_ne_top μ _), hmass_union, tsub_self]

end Problem356

end

end OAI
