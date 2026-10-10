import OAI.Analysis.CoulombTransport.GraphBridge

namespace OAI

universe uAlpha uIndex uKappa

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Problem356

section FiniteFibers

variable {α : Type uAlpha} {ι : Type uIndex} {κ : Type uKappa} [MeasurableSpace α]
    [Fintype ι] [Fintype κ] [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]

lemma sum_measure_pair_fibers (μ : Measure α) {p : α → ι} {q : α → κ}
    (hp : Measurable p) (hq : Measurable q) :
    (∑ i, ∑ j, μ {x | p x = i ∧ q x = j}) = μ Set.univ := by
  have h := sum_measure_preimage_singleton (μ := μ) (Finset.univ : Finset (ι × κ))
    (f := fun x => (p x, q x))
    (fun y _ => (hp.prodMk hq) (measurableSet_singleton y))
  simpa only [Finset.mem_univ, Finset.sum_const_zero,
    Finset.coe_univ, Set.preimage_univ, Fintype.sum_prod_type, Set.preimage, Set.mem_singleton_iff,
    Prod.mk.injEq, Set.mem_univ, Set.ofPred_true] using h

lemma sum_measure_pair_fibers_on (μ : Measure α) {s : Set α}
    (_hs : MeasurableSet s) {p : α → ι} {q : α → κ}
    (hp : Measurable p) (hq : Measurable q) :
    (∑ i, ∑ j, μ {x | x ∈ s ∧ p x = i ∧ q x = j}) = μ s := by
  calc
    _ = ∑ i, ∑ j, (μ.restrict s) {x | p x = i ∧ q x = j} := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hcell : MeasurableSet {x | p x = i ∧ q x = j} := by
        convert (hp (measurableSet_singleton i)).inter (hq (measurableSet_singleton j)) using 1
        ext x
        simp
      rw [Measure.restrict_apply hcell]
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, and_comm]
    _ = (μ.restrict s) Set.univ := sum_measure_pair_fibers (μ.restrict s) hp hq
    _ = μ s := by simp

end FiniteFibers

section CellTable

variable {ι : Type uIndex} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The joint finite-cell mass table of a triple measure. -/
def cellTable (p : E3 → ι) (π : Measure Triple) (i j k : ι) : ℝ≥0∞ :=
  π {t | p (tripleFst t) = i ∧ p (tripleSnd t) = j ∧ p (tripleThd t) = k}

lemma cellTable_sum_fst {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) (i : ι) :
    (∑ j, ∑ k, cellTable p π i j k) = μ (p ⁻¹' {i}) := by
  calc
    _ = π {t | p (tripleFst t) = i} :=
      sum_measure_pair_fibers_on π ((hp.comp measurable_tripleFst)
        (measurableSet_singleton i)) (hp.comp measurable_tripleSnd)
          (hp.comp measurable_tripleThd)
    _ = (Measure.map tripleFst π) (p ⁻¹' {i}) := by
      rw [Measure.map_apply measurable_tripleFst (hp (measurableSet_singleton i))]
      rfl
    _ = μ (p ⁻¹' {i}) := by rw [hπ.2.1]

lemma cellTable_sum_snd {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) (j : ι) :
    (∑ i, ∑ k, cellTable p π i j k) = μ (p ⁻¹' {j}) := by
  have h := sum_measure_pair_fibers_on π ((hp.comp measurable_tripleSnd)
    (measurableSet_singleton j)) (hp.comp measurable_tripleFst)
      (hp.comp measurable_tripleThd)
  calc
    _ = π {t | p (tripleSnd t) = j} := by
      simpa only [cellTable, Set.preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, Function.comp_apply,
        and_assoc, and_left_comm] using h
    _ = (Measure.map tripleSnd π) (p ⁻¹' {j}) := by
      rw [Measure.map_apply measurable_tripleSnd (hp (measurableSet_singleton j))]
      rfl
    _ = μ (p ⁻¹' {j}) := by rw [hπ.2.2.1]

lemma cellTable_sum_thd {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) (k : ι) :
    (∑ i, ∑ j, cellTable p π i j k) = μ (p ⁻¹' {k}) := by
  have h := sum_measure_pair_fibers_on π ((hp.comp measurable_tripleThd)
    (measurableSet_singleton k)) (hp.comp measurable_tripleFst)
      (hp.comp measurable_tripleSnd)
  calc
    _ = π {t | p (tripleThd t) = k} := by
      simpa only [cellTable, Set.preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, Function.comp_apply,
        and_assoc, and_comm, and_left_comm] using h
    _ = (Measure.map tripleThd π) (p ⁻¹' {k}) := by
      rw [Measure.map_apply measurable_tripleThd (hp (measurableSet_singleton k))]
      rfl
    _ = μ (p ⁻¹' {k}) := by rw [hπ.2.2.2]

lemma cellTable_le_fst {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) (i j k : ι) :
    cellTable p π i j k ≤ μ (p ⁻¹' {i}) := by
  calc
    _ ≤ ∑ k', cellTable p π i j k' :=
      Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ k)
    _ ≤ ∑ j', ∑ k', cellTable p π i j' k' :=
      Finset.single_le_sum (f := fun j' => ∑ k', cellTable p π i j' k') (fun _ _ => zero_le) (Finset.mem_univ j)
    _ = _ := cellTable_sum_fst hπ hp i

lemma cellTable_le_snd {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) (i j k : ι) :
    cellTable p π i j k ≤ μ (p ⁻¹' {j}) := by
  calc
    _ ≤ ∑ k', cellTable p π i j k' :=
      Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ k)
    _ ≤ ∑ i', ∑ k', cellTable p π i' j k' :=
      Finset.single_le_sum (f := fun i' => ∑ k', cellTable p π i' j k') (fun _ _ => zero_le) (Finset.mem_univ i)
    _ = _ := cellTable_sum_snd hπ hp j

lemma cellTable_le_thd {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) (i j k : ι) :
    cellTable p π i j k ≤ μ (p ⁻¹' {k}) := by
  calc
    _ ≤ ∑ j', cellTable p π i j' k :=
      Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', cellTable p π i' j' k :=
      Finset.single_le_sum (f := fun i' => ∑ j', cellTable p π i' j' k) (fun _ _ => zero_le) (Finset.mem_univ i)
    _ = _ := cellTable_sum_thd hπ hp k

lemma cellTable_pos_cell_masses_pos {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) {i j k : ι}
    (h : 0 < cellTable p π i j k) :
    0 < μ (p ⁻¹' {i}) ∧ 0 < μ (p ⁻¹' {j}) ∧ 0 < μ (p ⁻¹' {k}) :=
  ⟨h.trans_le (cellTable_le_fst hπ hp i j k),
    h.trans_le (cellTable_le_snd hπ hp i j k),
    h.trans_le (cellTable_le_thd hπ hp i j k)⟩

/-- The product label map corresponding to the cell table. -/
def tripleCellLabel (p : E3 → ι) (t : Triple) : ι × (ι × ι) :=
  (p (tripleFst t), (p (tripleSnd t), p (tripleThd t)))

omit [Fintype ι] [MeasurableSingletonClass ι] in
lemma measurable_tripleCellLabel {p : E3 → ι} (hp : Measurable p) :
    Measurable (tripleCellLabel p) :=
  (hp.comp measurable_tripleFst).prodMk
    ((hp.comp measurable_tripleSnd).prodMk (hp.comp measurable_tripleThd))

omit [Fintype ι] in
lemma cellTable_eq_map_singleton {p : E3 → ι} (hp : Measurable p)
    (π : Measure Triple) (i j k : ι) :
    cellTable p π i j k = (Measure.map (tripleCellLabel p) π) {(i, (j, k))} := by
  rw [cellTable, Measure.map_apply (measurable_tripleCellLabel hp) (measurableSet_singleton _)]
  congr 1
  ext t
  simp [tripleCellLabel, Set.mem_preimage]

lemma tripleCellLabel_map_eq_of_table_eq {p : E3 → ι} (hp : Measurable p)
    {π π' : Measure Triple}
    (h : ∀ i j k, cellTable p π i j k = cellTable p π' i j k) :
    Measure.map (tripleCellLabel p) π = Measure.map (tripleCellLabel p) π' := by
  apply Measure.ext_of_singleton
  rintro ⟨i, j, k⟩
  rw [← cellTable_eq_map_singleton hp, ← cellTable_eq_map_singleton hp]
  exact h i j k

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma cellTable_lt_top {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) (p : E3 → ι) (i j k : ι) :
    cellTable p π i j k < ⊤ := by
  have := hπ.1
  exact measure_lt_top π _

lemma cellTable_sum {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {p : E3 → ι} (hp : Measurable p) :
    (∑ i, ∑ j, ∑ k, cellTable p π i j k) = 1 := by
  have hsum := sum_measure_pair_fibers π (hp.comp measurable_tripleFst)
    ((hp.comp measurable_tripleSnd).prodMk (hp.comp measurable_tripleThd))
  have := hπ.1
  simpa only [cellTable, Fintype.sum_prod_type, Prod.mk.injEq,
    Function.comp_apply, measure_univ] using hsum

end CellTable

end Problem356

end

end OAI
