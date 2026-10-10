import OAI.NumberTheory.TwoPoint.Walks.BlockFamilyDecoding
import OAI.NumberTheory.TwoPoint.Bounds.ObservedColumnNames

namespace OAI

/-! Every regular perfect class inherits the bounds and injectivity of its forest line. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α] {n N : ℕ}

omit [DecidableEq α] in
theorem perfect_label_entry (label : Fin n → α) (perfect : Finset (Fin n))
    (chunks : List (List α ⊕ α))
    (hentries : columnChunkEntries chunks =
      (columnPositionEntries perfect).map (fun p => (label p.1, p.2)))
    (i : Fin n) (hi : i ∈ perfect) : (label i, true) ∈ columnChunkEntries chunks := by
  rw [hentries]
  simp only [columnPositionEntries, List.map_ofFn, Function.comp_def]
  apply List.mem_ofFn.mpr
  exact ⟨i, by simp [hi]⟩

omit [DecidableEq α] in
theorem perfect_label_position (label : Fin n → α) (perfect : Finset (Fin n))
    (chunks : List (List α ⊕ α))
    (hentries : columnChunkEntries chunks =
      (columnPositionEntries perfect).map (fun p => (label p.1, p.2)))
    (a : α) (ha : (a, true) ∈ columnChunkEntries chunks) :
    ∃ i ∈ perfect, label i = a := by
  rw [hentries] at ha
  simp only [columnPositionEntries, List.map_ofFn, Function.comp_def, List.mem_ofFn] at ha
  obtain ⟨i, he⟩ := ha
  have hlabel : label i = a := congrArg Prod.fst he
  have hperfect : decide (i ∈ perfect) = true := congrArg Prod.snd he
  exact ⟨i, of_decide_eq_true hperfect, hlabel⟩

/-- Coverage makes the shared forest bounds and injectivity apply to every
perfect regular occurrence, including those suppressed by run compression. -/
theorem regular_family_name_properties (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (lineNumber : α → ℕ)
    (hnumber : ∀ z (hz : z ∈ regular), lineNumber z = number ⟨z, hz⟩)
    (labelNat : ℕ → α)
    (chunks : List (List α ⊕ α)) (blocks : List (ℕ × ℕ))
    (hentries : columnChunkEntries chunks =
      (columnPositionEntries perfect).map (fun p => (label p.1, p.2)))
    (hblocks : chunks.filterMap (Sum.elim some (fun _ => none)) =
      blocks.map (fun b => blockLabelList labelNat b.1 b.2))
    (hbound : ∀ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
      ∀ p ∈ segment, lineNumber p.2 < N)
    (hinj : ∀ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
      ∀ p ∈ segment,
      ∀ other ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
      ∀ q ∈ other, lineNumber p.2 = lineNumber q.2 → p.2 = q.2) :
    (∀ i ∈ perfect, ∀ hi : label i ∈ regular, number ⟨label i, hi⟩ < N) ∧
    (∀ i ∈ perfect, ∀ j ∈ perfect, ∀ (hi : label i ∈ regular) (hj : label j ∈ regular),
      number ⟨label i, hi⟩ = number ⟨label j, hj⟩ → label i = label j) := by
  have hcover (i : Fin n) (hi : i ∈ perfect) (hr : label i ∈ regular) :
      ∃ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
        ∃ p ∈ segment, p.2 = label i := by
    exact perfect_regular_entry_covered labelNat (fun z => decide (z ∉ regular)) chunks blocks
      hblocks (label i) (perfect_label_entry label perfect chunks hentries i hi) (by simp [hr])
  have hnamed (i : Fin n) (hi : label i ∈ regular) (p : ℕ × α) (hp : p.2 = label i) :
      lineNumber p.2 = number ⟨label i, hi⟩ := by
    rw [hp]
    exact hnumber (label i) hi
  constructor
  · intro i hi hr
    obtain ⟨segment, hs, p, hp, he⟩ := hcover i hi hr
    simpa only [hnamed i hr p he] using hbound segment hs p hp
  · intro i hi j hj hri hrj heq
    obtain ⟨segment, hs, p, hp, hpi⟩ := hcover i hi hri
    obtain ⟨other, ho, q, hq, hqj⟩ := hcover j hj hrj
    have he : lineNumber p.2 = lineNumber q.2 := by
      simpa only [hnamed i hri p hpi, hnamed j hrj q hqj] using heq
    exact hpi.symm.trans ((hinj segment hs p hp other ho q hq he).trans hqj)

end TwoPointCorrelations

end OAI
