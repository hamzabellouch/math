import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Sets

namespace OAI

namespace MatchingFPRAS.Transport
variable {V E L : Type*}
namespace IndexedCycle

variable {bags : V → Finset L}

variable (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

lemma current_color_mem (i : ℤ) : (c.edgeAtZ i).color ∈ bags (c.vertexAtZ i) :=
  BagEdge.color_mem _ ((c.edgeAtZ_incidence i _).mpr (Or.inl rfl))

lemma previous_color_mem (i : ℤ) : (c.edgeAtZ (i-1)).color ∈ bags (c.vertexAtZ i) := by
  apply BagEdge.color_mem
  apply (c.edgeAtZ_incidence (i-1) _).mpr
  right
  congr 1
  omega

def labelCycle : MatchingFPRAS.Cells.CycleData G c.size where
  labels i := (c.edgeAtZ i).color
  periodic i := by rw [c.edgeAtZ_periodic]
  adjacent i := hbags (c.vertexAtZ i) _ (c.previous_color_mem i) _ (c.current_color_mem i)

variable [DecidableEq L]

lemma labelCycle_sets_subset (i : ℤ) : (c.labelCycle hbags).sets i ⊆ bags (c.vertexAtZ i) := by
  intro l hl
  simp only [MatchingFPRAS.Cells.CycleData.sets, labelCycle,
    Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact c.previous_color_mem i
  · exact c.current_color_mem i

lemma admissible_common_bag {x y : ℕ} (h : (c.labelCycle hbags).Admissible x y) :
    ∃ l, l ∈ bags (c.vertexAt x) ∧ l ∈ bags (c.vertexAt y) := by
  obtain ⟨l, hlx, hly⟩ := h
  refine ⟨l, ?_, ?_⟩
  · simpa [c.vertexAtZ_nat] using c.labelCycle_sets_subset hbags x hlx
  · simpa [c.vertexAtZ_nat] using c.labelCycle_sets_subset hbags y hly

lemma labelSets_periodic (i : ℤ) :
    (c.labelCycle hbags).sets (i+c.size) = (c.labelCycle hbags).sets i := by
  have h : i + (c.size : ℤ) - 1 = (i-1) + c.size := by ring
  simp only [MatchingFPRAS.Cells.CycleData.sets, labelCycle, h, c.edgeAtZ_periodic]

lemma edge_color_fixed (i : ℕ) :
    (c.edgeAt i).color ∈ (c.labelCycle hbags).sets i ∧
    (c.edgeAt i).color ∈ (c.labelCycle hbags).sets (i+1) := by
  have h : (c.edgeAtZ (i : ℤ)).color ∈ (c.labelCycle hbags).sets (i : ℤ) ∧
      (c.edgeAtZ (i : ℤ)).color ∈ (c.labelCycle hbags).sets ((i : ℤ)+1) := by
    simp [MatchingFPRAS.Cells.CycleData.sets, labelCycle]
  simpa only [c.edgeAtZ_nat] using h

noncomputable def chord (x y : ℕ) (hxy : x < y) (hy : y < c.size)
    (ha : (c.labelCycle hbags).Admissible x y) : BagEdge bags := by
  classical
  exact if hshort : y = x+1 then c.edgeAt x
    else if hwrap : x = 0 ∧ y+1 = c.size then c.edgeAt y
    else
      let l := ha.choose
      BagEdge.ofEndpoints (c.vertexAt x) (c.vertexAt y)
        (fun h => by
          have := (c.vertexAt_eq_iff (a := 0) (by have := c.four_le; omega)
            ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).mp h
          omega) l
        (by simpa [c.vertexAtZ_nat] using c.labelCycle_sets_subset hbags x ha.choose_spec.1)
        (by simpa [c.vertexAtZ_nat] using c.labelCycle_sets_subset hbags y ha.choose_spec.2)

lemma chord_incidence (x y : ℕ) (hxy : x < y) (hy : y < c.size)
    (ha : (c.labelCycle hbags).Admissible x y) (v : V) :
    (c.chord hbags x y hxy hy ha).Incident v ↔ v = c.vertexAt x ∨ v = c.vertexAt y := by
  classical
  dsimp only [chord]
  split_ifs with hshort hwrap
  · simpa [hshort] using c.edgeAt_incidence x v
  · rw [c.edgeAt_incidence]
    have he : c.vertexAt (y+1) = c.vertexAt x := by
      rw [hwrap.2, hwrap.1]
      simpa using c.vertexAt_periodic 0
    rw [he]
    tauto
  · exact BagEdge.ofEndpoints_incidence _ _ _ _ _ _ _

lemma chord_short (x y : ℕ) (hxy : x < y) (hy : y < c.size)
    (ha : (c.labelCycle hbags).Admissible x y) (h : y = x+1) :
    c.chord hbags x y hxy hy ha = c.edgeAt x := by
  simp only [chord, dite_eq_left h]

lemma chord_wrap (x y : ℕ) (hxy : x < y) (hy : y < c.size)
    (ha : (c.labelCycle hbags).Admissible x y) (h : x = 0 ∧ y+1 = c.size) :
    c.chord hbags x y hxy hy ha = c.edgeAt y := by
  have hn : y ≠ x+1 := by have := c.four_le; omega
  simp only [chord, dite_eq_right hn, dite_eq_left h]

lemma chord_color_fixed (x y : ℕ) (hxy : x < y) (hy : y < c.size)
    (ha : (c.labelCycle hbags).Admissible x y) :
    (c.chord hbags x y hxy hy ha).color ∈ (c.labelCycle hbags).sets x ∧
    (c.chord hbags x y hxy hy ha).color ∈ (c.labelCycle hbags).sets y := by
  classical
  dsimp only [chord]
  split_ifs with hs hw
  · simpa only [hs, Nat.cast_add, Nat.cast_one] using c.edge_color_fixed hbags x
  · have hb := c.edge_color_fixed hbags y
    refine ⟨?_, hb.1⟩
    have he : (y : ℤ)+1 = (0 : ℤ)+c.size := by omega
    rw [he, c.labelSets_periodic hbags] at hb
    simpa only [hw.1, Nat.cast_zero] using hb.2
  · exact ha.choose_spec

def cellCorners {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) : c.Corners where
  a₀ := x
  a₁ := p
  a₂ := q
  a₃ := y
  lt₀ := hc.first_pos
  lt₁ := hc.middle_pos
  lt₂ := hc.third_pos
  lt₃ := hy
  odd₀ := hc.odd_first
  odd₁ := hc.odd_middle
  odd₂ := hc.odd_third
  odd₃ := by
    have he : c.size + x - y = c.size - (y-x) := by have := hc.first_pos; have := hc.middle_pos; have := hc.third_pos; omega
    rw [he]
    exact hc.odd_exterior

noncomputable def cellChords {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) : Fin 4 → BagEdge bags :=
  ![c.chord hbags x p hc.first_pos (by have := hc.middle_pos; have := hc.third_pos; omega) hc.first,
    c.chord hbags p q hc.middle_pos (by have := hc.third_pos; omega) hc.middle,
    c.chord hbags q y hc.third_pos hy hc.third,
    c.chord hbags x y (by have := hc.first_pos; have := hc.middle_pos; have := hc.third_pos; omega)
      hy (by obtain ⟨l, hly, hlx⟩ := hc.exterior; exact ⟨l,hlx,hly⟩)]

lemma cellChords_incidence {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i : Fin 4) (v : V) :
    (c.cellChords hbags hc hy i).Incident v ↔
      v = ((c.cellCorners hbags hc hy).side i).vertex 0 ∨
      v = ((c.cellCorners hbags hc hy).side i).vertex
        ((c.cellCorners hbags hc hy).side i).length := by
  simp only [Corners.side_first, Corners.side_last]
  have hper : c.vertexAt (c.size+x) = c.vertexAt x := by
    simpa only [Nat.add_comm] using c.vertexAt_periodic x
  fin_cases i <;> simp [cellChords, chord_incidence, cellCorners, Corners.start,
    Corners.stop, hper, or_comm]

noncomputable def pathsOfCell [DecidableEq V] {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) : CellPaths (BagEdge.Incident (bags := bags)) :=
  (c.cellCorners hbags hc hy).cellPaths (c.cellChords hbags hc hy)
    (c.cellChords_incidence hbags hc hy)

def sideGood (k : c.Corners) (i : Fin 4) : Prop :=
  k.length i = 1 ∨ ∃ l, l ∈ (c.labelCycle hbags).sets (k.start i+1) ∧
    l ∈ (c.labelCycle hbags).sets ((k.stop i : ℤ)-1)

lemma cell_sideGood {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i : Fin 4) :
    c.sideGood hbags (c.cellCorners hbags hc hy) i ↔
      ![(c.labelCycle hbags).Good x p, (c.labelCycle hbags).Good p q,
        (c.labelCycle hbags).Good q y, (c.labelCycle hbags).ExteriorGood x y] i := by
  have hxp := hc.first_pos
  have hpq := hc.middle_pos
  have hqy := hc.third_pos
  have cast_sub (a : ℕ) (ha : 1 ≤ a) : ((a-1 : ℕ) : ℤ) = (a : ℤ)-1 := by omega
  have he : ((c.size : ℤ)+(x : ℤ))-1 = ((x : ℤ)-1) + c.size := by ring
  fin_cases i <;> simp only [sideGood, cellCorners, Corners.length, Corners.start,
    Corners.stop]
  · simp [MatchingFPRAS.Cells.CycleData.Good, MatchingFPRAS.Cells.CycleData.Admissible,
      cast_sub p (by omega), Nat.cast_add, Nat.cast_one, show p-x=1 ↔ p=x+1 by omega]
  · simp [MatchingFPRAS.Cells.CycleData.Good, MatchingFPRAS.Cells.CycleData.Admissible,
      cast_sub q (by omega), Nat.cast_add, Nat.cast_one, show q-p=1 ↔ q=p+1 by omega]
  · simp [MatchingFPRAS.Cells.CycleData.Good, MatchingFPRAS.Cells.CycleData.Admissible,
      cast_sub y (by omega), Nat.cast_add, Nat.cast_one, show y-q=1 ↔ y=q+1 by omega]
  · simp [MatchingFPRAS.Cells.CycleData.ExteriorGood, Nat.cast_add, he,
      c.labelSets_periodic hbags, show c.size+x-y=1 ↔ y+1=x+c.size by omega]

noncomputable def leafRepair (k : c.Corners) (i : Fin 4) : BagEdge bags := by
  classical
  exact if hg : c.sideGood hbags k i ∧ k.length i ≠ 1 then
    let hl := hg.1.resolve_left hg.2
    BagEdge.ofEndpoints ((k.side i).vertex 1) ((k.side i).vertex ((k.side i).length-1))
      (by
        have hp := (k.side i).positive
        have ho := (k.side i).odd
        have hn : (k.side i).length ≠ 1 := hg.2
        intro he
        have hh := (k.side i).simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ he
        omega)
      hl.choose
      (by
        have hm := c.labelCycle_sets_subset hbags (k.start i+1) hl.choose_spec.1
        have hv : c.vertexAtZ ((k.start i : ℤ)+1) = (k.side i).vertex 1 := by
          simpa only [Corners.side_vertex, Nat.cast_add, Nat.cast_one] using c.vertexAtZ_nat (k.start i+1)
        exact (congrArg (fun v => hl.choose ∈ bags v) hv).mp hm)
      (by
        have hm := c.labelCycle_sets_subset hbags ((k.stop i : ℤ)-1) hl.choose_spec.2
        have hb := k.bounds i
        have he : ((k.stop i : ℤ)-1) = ((k.start i + ((k.side i).length-1) : ℕ) : ℤ) := by
          rw [Corners.side_length]
          dsimp [Corners.length]
          omega
        have hv : c.vertexAtZ ((k.stop i : ℤ)-1) = (k.side i).vertex ((k.side i).length-1) := by
          rw [he, c.vertexAtZ_nat]
          rfl
        exact (congrArg (fun v => hl.choose ∈ bags v) hv).mp hm)
  else c.edgeAt (k.start i)

lemma leafRepair_incidence (k : c.Corners) (i : Fin 4)
    (hg : c.sideGood hbags k i) (hl : k.length i ≠ 1) (v : V) :
    (c.leafRepair hbags k i).Incident v ↔
      v = (k.side i).vertex 1 ∨ v = (k.side i).vertex ((k.side i).length-1) := by
  simp only [leafRepair, dite_eq_left (And.intro hg hl), BagEdge.ofEndpoints_incidence]

lemma leafRepair_color_fixed (k : c.Corners) (i : Fin 4)
    (hg : c.sideGood hbags k i) (hl : k.length i ≠ 1) :
    (c.leafRepair hbags k i).color ∈ (c.labelCycle hbags).sets (k.start i+1) ∧
    (c.leafRepair hbags k i).color ∈ (c.labelCycle hbags).sets ((k.stop i : ℤ)-1) := by
  simp only [leafRepair, dite_eq_left (And.intro hg hl), BagEdge.ofEndpoints_color]
  exact (hg.resolve_left hl).choose_spec

lemma cell_has_good_pair {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) :
    ∃ b : Bool, ∀ i : Fin 4, CellPaths.sideBit i ≠ b →
      c.sideGood hbags (c.cellCorners hbags hc hy) i := by
  rcases hc.some_good with ⟨hf,ht⟩ | ⟨hm,he⟩
  · refine ⟨false, ?_⟩
    intro i hi
    rw [c.cell_sideGood hbags hc hy]
    fin_cases i <;> simp_all [CellPaths.sideBit]
  · refine ⟨true, ?_⟩
    intro i hi
    rw [c.cell_sideGood hbags hc hy]
    fin_cases i <;> simp_all [CellPaths.sideBit]

lemma cell_actual_repairs [DecidableEq V] {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (b : Bool)
    (hg : ∀ i : Fin 4, CellPaths.sideBit i ≠ b →
      c.sideGood hbags (c.cellCorners hbags hc hy) i) :
    (c.pathsOfCell hbags hc hy).Repairs b
      (c.leafRepair hbags (c.cellCorners hbags hc hy)) := by
  intro i hi hl v
  exact c.leafRepair_incidence hbags _ i (hg i hi) hl v

lemma cell_long_opposite_good {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (b : Bool)
    (hl : ∀ i : Fin 4, CellPaths.sideBit i = b →
      (c.cellCorners hbags hc hy).length i ≠ 1) :
    ∀ i : Fin 4, CellPaths.sideBit i ≠ b →
      c.sideGood hbags (c.cellCorners hbags hc hy) i := by
  have hxp := hc.first_pos
  have hpq := hc.middle_pos
  have hqy := hc.third_pos
  cases b
  · have h₁ := hl 1 (by decide)
    have h₃ := hl 3 (by decide)
    simp only [Corners.length, Corners.start, Corners.stop, cellCorners] at h₁ h₃
    have hg := hc.middle_exterior_long (by dsimp at h₁; omega) (by dsimp at h₃; omega)
    intro i hi
    rw [c.cell_sideGood hbags hc hy]
    fin_cases i <;> simp_all [CellPaths.sideBit]
  · have h₀ := hl 0 (by decide)
    have h₂ := hl 2 (by decide)
    simp only [Corners.length, Corners.start, Corners.stop, cellCorners] at h₀ h₂
    have hg := hc.outer_long (by dsimp at h₀; omega) (by dsimp at h₂; omega)
    intro i hi
    rw [c.cell_sideGood hbags hc hy]
    fin_cases i <;> simp_all [CellPaths.sideBit]

lemma cellChords_fixed {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i : Fin 4) :
    (c.cellChords hbags hc hy i).color ∈
      (c.labelCycle hbags).sets ((c.cellCorners hbags hc hy).start i) ∧
    (c.cellChords hbags hc hy i).color ∈
      (c.labelCycle hbags).sets ((c.cellCorners hbags hc hy).stop i) := by
  fin_cases i
  · exact c.chord_color_fixed hbags x p hc.first_pos
      (by have := hc.middle_pos; have := hc.third_pos; omega) hc.first
  · exact c.chord_color_fixed hbags p q hc.middle_pos
      (by have := hc.third_pos; omega) hc.middle
  · exact c.chord_color_fixed hbags q y hc.third_pos hy hc.third
  · have hb := c.chord_color_fixed hbags x y
      (by have := hc.first_pos; have := hc.middle_pos; have := hc.third_pos; omega) hy
      (by obtain ⟨l,hly,hlx⟩ := hc.exterior; exact ⟨l,hlx,hly⟩)
    change _ ∈ (c.labelCycle hbags).sets y ∧ _ ∈ (c.labelCycle hbags).sets (c.size+x)
    rw [add_comm, c.labelSets_periodic hbags]
    exact ⟨hb.2,hb.1⟩

lemma cellChords_previous_fixed {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i : Fin 4) :
    (c.cellChords hbags hc hy (i+1)).color ∈
      (c.labelCycle hbags).sets ((c.cellCorners hbags hc hy).stop i) := by
  have h := (c.cellChords_fixed hbags hc hy (i+1)).1
  fin_cases i
  · exact h
  · exact h
  · exact h
  · change _ ∈ (c.labelCycle hbags).sets (c.size+x)
    rw [add_comm, c.labelSets_periodic hbags]
    exact h

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

include hheight hstep in
lemma fixed_height_ratio (i : ℤ) {a b : L}
    (ha : a ∈ (c.labelCycle hbags).sets i) (hb : b ∈ (c.labelCycle hbags).sets i) :
    height a ≤ 2 * height b := by
  rcases (c.labelCycle hbags).sets_clique i a ha b hb with rfl | hab
  · linarith [hheight a]
  · exact hstep a b hab

include hheight hstep in
lemma cellChords_height_ratio {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i j : Fin 4) :
    height (c.cellChords hbags hc hy i).color ≤ 4 * height (c.cellChords hbags hc hy j).color := by
  have hn (i : Fin 4) :
      height (c.cellChords hbags hc hy i).color ≤ 2 * height (c.cellChords hbags hc hy (i+1)).color ∧
      height (c.cellChords hbags hc hy (i+1)).color ≤ 2 * height (c.cellChords hbags hc hy i).color := by
    exact ⟨c.fixed_height_ratio hbags height hheight hstep _
      (c.cellChords_fixed hbags hc hy i).2 (c.cellChords_previous_fixed hbags hc hy i),
      c.fixed_height_ratio hbags height hheight hstep _
      (c.cellChords_previous_fixed hbags hc hy i) (c.cellChords_fixed hbags hc hy i).2⟩
  have h₀ := hn 0
  have h₁ := hn 1
  have h₂ := hn 2
  have h₃ := hn 3
  change height (c.cellChords hbags hc hy 0).color ≤ 2 * height (c.cellChords hbags hc hy 1).color ∧
    height (c.cellChords hbags hc hy 1).color ≤ 2 * height (c.cellChords hbags hc hy 0).color at h₀
  change height (c.cellChords hbags hc hy 1).color ≤ 2 * height (c.cellChords hbags hc hy 2).color ∧
    height (c.cellChords hbags hc hy 2).color ≤ 2 * height (c.cellChords hbags hc hy 1).color at h₁
  change height (c.cellChords hbags hc hy 2).color ≤ 2 * height (c.cellChords hbags hc hy 3).color ∧
    height (c.cellChords hbags hc hy 3).color ≤ 2 * height (c.cellChords hbags hc hy 2).color at h₂
  change height (c.cellChords hbags hc hy 3).color ≤ 2 * height (c.cellChords hbags hc hy 0).color ∧
    height (c.cellChords hbags hc hy 0).color ≤ 2 * height (c.cellChords hbags hc hy 3).color at h₃
  have hp₀ := hheight (c.cellChords hbags hc hy 0).color
  have hp₁ := hheight (c.cellChords hbags hc hy 1).color
  have hp₂ := hheight (c.cellChords hbags hc hy 2).color
  have hp₃ := hheight (c.cellChords hbags hc hy 3).color
  rcases h₀ with ⟨h₀,h₀'⟩
  rcases h₁ with ⟨h₁,h₁'⟩
  rcases h₂ with ⟨h₂,h₂'⟩
  rcases h₃ with ⟨h₃,h₃'⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl <;> linarith

def LocalEdge {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (e : BagEdge bags) : Prop :=
  ∃ i : Fin 4, e = c.cellChords hbags hc hy i ∨
    e = ((c.cellCorners hbags hc hy).side i).edge 0 ∨
    e = ((c.cellCorners hbags hc hy).side i).edge
        (((c.cellCorners hbags hc hy).side i).length-1) ∨
    (c.sideGood hbags (c.cellCorners hbags hc hy) i ∧
      (c.cellCorners hbags hc hy).length i ≠ 1 ∧
      e = c.leafRepair hbags (c.cellCorners hbags hc hy) i)

lemma side_boundaries_fixed (k : c.Corners) (i : Fin 4) :
    ((k.side i).edge 0).color ∈ (c.labelCycle hbags).sets (k.start i) ∧
    ((k.side i).edge 0).color ∈ (c.labelCycle hbags).sets (k.start i+1) ∧
    ((k.side i).edge ((k.side i).length-1)).color ∈ (c.labelCycle hbags).sets ((k.stop i : ℤ)-1) ∧
    ((k.side i).edge ((k.side i).length-1)).color ∈ (c.labelCycle hbags).sets (k.stop i) := by
  have hb := k.bounds i
  have he : k.start i + (k.length i-1) = k.stop i-1 := by dsimp [Corners.length]; omega
  change (c.edgeAt (k.start i+0)).color ∈ _ ∧ (c.edgeAt (k.start i+0)).color ∈ _ ∧
    (c.edgeAt (k.start i + (k.length i-1))).color ∈ _ ∧
    (c.edgeAt (k.start i + (k.length i-1))).color ∈ _
  rw [Nat.add_zero, he]
  have hs := c.edge_color_fixed hbags (k.start i)
  have ht := c.edge_color_fixed hbags (k.stop i-1)
  have hcast : ((k.stop i-1 : ℕ) : ℤ) = (k.stop i : ℤ)-1 := by omega
  have hcast' : ((k.stop i-1 : ℕ) : ℤ)+1 = (k.stop i : ℤ) := by omega
  exact ⟨hs.1, hs.2, by simpa only [hcast] using ht.1, by simpa only [hcast'] using ht.2⟩

include hheight hstep in
lemma localEdge_height_ratio {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) {e : BagEdge bags} (he : c.LocalEdge hbags hc hy e) :
    ∃ i : Fin 4,
      height e.color ≤ 4 * height (c.cellChords hbags hc hy i).color ∧
      height (c.cellChords hbags hc hy i).color ≤ 4 * height e.color := by
  obtain ⟨i,he⟩ := he
  refine ⟨i,?_⟩
  have hh := hheight e.color
  have hch := hheight (c.cellChords hbags hc hy i).color
  have hbc := c.side_boundaries_fixed hbags (c.cellCorners hbags hc hy) i
  have hc' := c.cellChords_fixed hbags hc hy i
  rcases he with rfl | rfl | rfl | ⟨hg,hl,rfl⟩
  · constructor <;> linarith
  · have h₁ := c.fixed_height_ratio hbags height hheight hstep _ hbc.1 hc'.1
    have h₂ := c.fixed_height_ratio hbags height hheight hstep _ hc'.1 hbc.1
    constructor <;> linarith
  · have h₁ := c.fixed_height_ratio hbags height hheight hstep _ hbc.2.2.2 hc'.2
    have h₂ := c.fixed_height_ratio hbags height hheight hstep _ hc'.2 hbc.2.2.2
    constructor <;> linarith
  · have hrc := c.leafRepair_color_fixed hbags _ i hg hl
    have h₁ := c.fixed_height_ratio hbags height hheight hstep _ hrc.1 hbc.2.1
    have h₂ := c.fixed_height_ratio hbags height hheight hstep _ hbc.2.1 hrc.1
    have h₃ := c.fixed_height_ratio hbags height hheight hstep _ hbc.1 hc'.1
    have h₄ := c.fixed_height_ratio hbags height hheight hstep _ hc'.1 hbc.1
    constructor <;> linarith

include hheight hstep in

theorem cell_comparability {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)
    (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)
    {e f : BagEdge bags} (he : c.LocalEdge hbags hc hy e) (hf : c.LocalEdge hbags hc hy f) :
    w e ≤ (1000 * D) * w f := by
  obtain ⟨i,hei,hie⟩ := c.localEdge_height_ratio hbags height hheight hstep hc hy he
  obtain ⟨j,hfj,hjf⟩ := c.localEdge_height_ratio hbags height hheight hstep hc hy hf
  have hij := c.cellChords_height_ratio hbags height hheight hstep hc hy i j
  have hh : height e.color ≤ 64 * height f.color := by linarith
  have hDpos : 0 < D := by linarith
  have hfpos : 0 < w f := lt_of_lt_of_le (div_pos (hheight f.color) hDpos) (hw f).1
  have hlo : height f.color ≤ w f * D := (div_le_iff₀ hDpos).mp (hw f).1
  have h192 : w e ≤ 192 * D * w f := by nlinarith [(hw e).2]
  nlinarith [mul_pos hDpos hfpos]

lemma common_clamp_ratio {lo hi A x y : ℝ} (hlo : 0 ≤ lo) (hA : 1 ≤ A)
    (hxy : x ≤ A * y) :
    max lo (min hi x) ≤ A * max lo (min hi y) := by
  have hnonneg : 0 ≤ max lo (min hi y) := le_trans hlo (le_max_left _ _)
  have hupper : max lo (min hi y) ≤ A * max lo (min hi y) := by nlinarith
  apply max_le
  · exact le_trans (le_max_left _ _) hupper
  · by_cases hy : y ≤ hi
    · have hm : y ≤ max lo (min hi y) := by rw [min_eq_right hy]; exact le_max_right _ _
      exact le_trans (min_le_right _ _) (le_trans hxy (mul_le_mul_of_nonneg_left hm (by linarith)))
    · have hm : hi ≤ max lo (min hi y) := by rw [min_eq_left (le_of_not_ge hy)]; exact le_max_right _ _
      exact le_trans (min_le_left _ _) (le_trans hm hupper)

include hheight hstep in
lemma cell_clamp_comparability {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)
    (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)
    (lo hi : ℝ) (hlo : 0 ≤ lo)
    {e f : BagEdge bags} (he : c.LocalEdge hbags hc hy e) (hf : c.LocalEdge hbags hc hy f) :
    max lo (min hi (w e)) ≤ (1000 * D) * max lo (min hi (w f)) :=
  common_clamp_ratio hlo (by linarith) (c.cell_comparability hbags height hheight hstep hc hy D hD w hw he hf)

lemma drops_local [DecidableEq V] {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (r : Bool) {e : BagEdge bags}
    (he : e ∈ (c.pathsOfCell hbags hc hy).drops r) : c.LocalEdge hbags hc hy e := by
  obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp he
  by_cases h : CellPaths.sideBit i = r
  · simp only [ite_eq_left h, Multiset.notMem_zero] at hi
  · simp only [ite_eq_right h, Finset.mem_val] at hi
    refine ⟨i, Or.inr ?_⟩
    change e ∈ ((c.cellCorners hbags hc hy).side i).boundary at hi
    by_cases hl : ((c.cellCorners hbags hc hy).side i).length = 1
    · simp only [OddPath.boundary, ite_eq_left hl, Finset.mem_singleton] at hi
      exact Or.inl hi
    · simp only [OddPath.boundary, ite_eq_right hl, Finset.mem_insert, Finset.mem_singleton] at hi
      exact hi.imp_right Or.inl

lemma additions_local [DecidableEq V] {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (b r : Bool)
    (hg : ∀ i, CellPaths.sideBit i ≠ r → c.sideGood hbags (c.cellCorners hbags hc hy) i)
    {e : BagEdge bags} (he : e ∈ (c.pathsOfCell hbags hc hy).additions b r
      (c.leafRepair hbags (c.cellCorners hbags hc hy))) : c.LocalEdge hbags hc hy e := by
  rcases Multiset.mem_add.mp he with he | he
  · obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp he
    by_cases h : CellPaths.sideBit i = b
    · simp only [ite_eq_left h, Multiset.mem_singleton] at hi
      exact ⟨i, Or.inl hi⟩
    · simp only [ite_eq_right h, Multiset.notMem_zero] at hi
  · obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp he
    by_cases h : CellPaths.sideBit i = r
    · simp only [ite_eq_left h, Multiset.notMem_zero] at hi
    · simp only [ite_eq_right h] at hi
      change e ∈ ((c.cellCorners hbags hc hy).side i).repairAdded (c.leafRepair hbags (c.cellCorners hbags hc hy) i) at hi
      by_cases hl : ((c.cellCorners hbags hc hy).side i).length = 1
      · simp only [OddPath.repairAdded, ite_eq_left hl, Multiset.notMem_zero] at hi
      · simp only [OddPath.repairAdded, ite_eq_right hl, Multiset.mem_singleton] at hi
        exact ⟨i, Or.inr (Or.inr (Or.inr ⟨hg i h, hl, hi⟩))⟩

end IndexedCycle

end MatchingFPRAS.Transport

end OAI
