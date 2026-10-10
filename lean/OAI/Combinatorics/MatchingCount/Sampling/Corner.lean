import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Span

namespace OAI

namespace MatchingFPRAS.Transport
variable {V L : Type*} [DecidableEq V]
variable {E : Type*} [DecidableEq E] (inc : E → V → Prop)
namespace CellPaths

variable {inc} (c : CellPaths inc)

def corner (i : Fin 4) : V := (c.side i).vertex 0

def vertices : Finset V :=
  ((c.side 0).inside ∪ (c.side 1).inside) ∪ ((c.side 2).inside ∪ (c.side 3).inside) ∪
    {c.corner 0, c.corner 1, c.corner 2, c.corner 3}

omit [DecidableEq E] in
lemma ends_eq (i : Fin 4) : (c.side i).ends = {c.corner i, c.corner (i+1)} := by
  simp only [OddPath.ends, c.joins, corner]

omit [DecidableEq E] in
lemma inside_disjoint_span (i j : Fin 4) (hij : i ≠ j) :
    Disjoint (c.side i).inside (c.side j).span := by
  rw [← (c.side j).inside_union_ends]
  exact Finset.disjoint_union_right.mpr
    ⟨c.interiors_disjoint hij, c.interior_ends_disjoint i j⟩

omit [DecidableEq E] in
lemma opposite_ends_even : Disjoint (c.side 0).ends (c.side 2).ends := by
  rw [c.ends_eq, c.ends_eq]
  apply Finset.disjoint_left.mpr
  intro v hv hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
  rcases hv with h | h <;> rcases hw with k | k
  all_goals have hh := c.corners_injective (h.symm.trans k)
  all_goals exact absurd hh (by decide)

omit [DecidableEq E] in
lemma opposite_ends_odd : Disjoint (c.side 1).ends (c.side 3).ends := by
  rw [c.ends_eq, c.ends_eq]
  apply Finset.disjoint_left.mpr
  intro v hv hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
  rcases hv with h | h <;> rcases hw with k | k
  all_goals have hh := c.corners_injective (h.symm.trans k)
  all_goals exact absurd hh (by decide)

omit [DecidableEq E] in
lemma opposite_span_even : Disjoint (c.side 0).span (c.side 2).span := by
  rw [← (c.side 0).inside_union_ends]
  apply Finset.disjoint_union_left.mpr
  refine ⟨c.inside_disjoint_span 0 2 (by decide), ?_⟩
  rw [← (c.side 2).inside_union_ends]
  exact Finset.disjoint_union_right.mpr ⟨(c.interior_ends_disjoint 2 0).symm,
    c.opposite_ends_even⟩

omit [DecidableEq E] in
lemma opposite_span_odd : Disjoint (c.side 1).span (c.side 3).span := by
  rw [← (c.side 1).inside_union_ends]
  apply Finset.disjoint_union_left.mpr
  refine ⟨c.inside_disjoint_span 1 3 (by decide), ?_⟩
  rw [← (c.side 3).inside_union_ends]
  exact Finset.disjoint_union_right.mpr ⟨(c.interior_ends_disjoint 3 1).symm,
    c.opposite_ends_odd⟩

omit [DecidableEq E] in
lemma even_blocks_union :
    ((c.side 0).span ∪ (c.side 2).span) ∪
      ((c.side 1).inside ∪ (c.side 3).inside) = c.vertices := by
  rw [← (c.side 0).inside_union_ends, ← (c.side 2).inside_union_ends,
    c.ends_eq, c.ends_eq]
  ext v
  simp only [vertices, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

omit [DecidableEq E] in
lemma odd_blocks_union :
    ((c.side 1).span ∪ (c.side 3).span) ∪
      ((c.side 0).inside ∪ (c.side 2).inside) = c.vertices := by
  rw [← (c.side 1).inside_union_ends, ← (c.side 3).inside_union_ends,
    c.ends_eq, c.ends_eq]
  ext v
  simp only [vertices, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

def assemble (M : Fin 4 → Finset E) : Finset E := (M 0 ∪ M 2) ∪ (M 1 ∪ M 3)

lemma matching_even_full (M : Fin 4 → Finset E)
    (h0 : MatchingOn inc (M 0) (c.side 0).span)
    (h2 : MatchingOn inc (M 2) (c.side 2).span)
    (h1 : MatchingOn inc (M 1) (c.side 1).inside)
    (h3 : MatchingOn inc (M 3) (c.side 3).inside) :
    MatchingOn inc (assemble M) c.vertices := by
  have h02 := h0.union h2 c.opposite_span_even
  have h13 := h1.union h3 (c.interiors_disjoint (by decide : (1 : Fin 4) ≠ 3))
  have hd : Disjoint ((c.side 0).span ∪ (c.side 2).span)
      ((c.side 1).inside ∪ (c.side 3).inside) := by
    simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
    exact ⟨⟨(c.inside_disjoint_span 1 0 (by decide)).symm,
      (c.inside_disjoint_span 1 2 (by decide)).symm⟩,
      ⟨(c.inside_disjoint_span 3 0 (by decide)).symm,
      (c.inside_disjoint_span 3 2 (by decide)).symm⟩⟩
  simpa only [c.even_blocks_union, assemble] using h02.union h13 hd

lemma matching_odd_full (M : Fin 4 → Finset E)
    (h0 : MatchingOn inc (M 0) (c.side 0).inside)
    (h2 : MatchingOn inc (M 2) (c.side 2).inside)
    (h1 : MatchingOn inc (M 1) (c.side 1).span)
    (h3 : MatchingOn inc (M 3) (c.side 3).span) :
    MatchingOn inc (assemble M) c.vertices := by
  have h02 := h0.union h2 (c.interiors_disjoint (by decide : (0 : Fin 4) ≠ 2))
  have h13 := h1.union h3 c.opposite_span_odd
  have hd : Disjoint ((c.side 0).inside ∪ (c.side 2).inside)
      ((c.side 1).span ∪ (c.side 3).span) := by
    simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
    exact ⟨⟨c.inside_disjoint_span 0 1 (by decide), c.inside_disjoint_span 2 1 (by decide)⟩,
      ⟨c.inside_disjoint_span 0 3 (by decide), c.inside_disjoint_span 2 3 (by decide)⟩⟩
  have hs : ((c.side 0).inside ∪ (c.side 2).inside) ∪
      ((c.side 1).span ∪ (c.side 3).span) = c.vertices :=
    (Finset.union_comm _ _).trans c.odd_blocks_union
  simpa only [hs, assemble] using h02.union h13 hd

def sideBit (i : Fin 4) : Bool := decide (i.val % 2 = 0)

def blocks (b : Bool) (i : Fin 4) : Finset V :=
  if sideBit i = b then (c.side i).span else (c.side i).inside

def pieces (b : Bool) (full inner : Fin 4 → Finset E) (i : Fin 4) : Finset E :=
  if sideBit i = b then full i else inner i

omit [DecidableEq E] in
lemma same_bit_spans (i j : Fin 4) (hij : i ≠ j) (hbit : sideBit i = sideBit j) :
    Disjoint (c.side i).span (c.side j).span := by
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals norm_num [sideBit] at hbit
  · exact c.opposite_span_even
  · exact c.opposite_span_odd
  · exact c.opposite_span_even.symm
  · exact c.opposite_span_odd.symm

omit [DecidableEq E] in
lemma blocks_disjoint (b : Bool) : Pairwise fun i j => Disjoint (c.blocks b i) (c.blocks b j) := by
  intro i j hij
  by_cases hi : sideBit i = b <;> by_cases hj : sideBit j = b
  · simp only [blocks, ite_eq_left hi, ite_eq_left hj]
    exact c.same_bit_spans i j hij (hi.trans hj.symm)
  · simp only [blocks, ite_eq_left hi, ite_eq_right hj]
    exact (c.inside_disjoint_span j i hij.symm).symm
  · simp only [blocks, ite_eq_right hi, ite_eq_left hj]
    exact c.inside_disjoint_span i j hij
  · simp only [blocks, ite_eq_right hi, ite_eq_right hj]
    exact c.interiors_disjoint hij

lemma assembled_matching (b : Bool) (M : Fin 4 → Finset E)
    (hM : ∀ i, MatchingOn inc (M i) (c.blocks b i)) :
    MatchingOn inc (assemble M) c.vertices := by
  cases b
  · apply c.matching_odd_full M <;> first
      | simpa [blocks, sideBit] using hM 0
      | simpa [blocks, sideBit] using hM 1
      | simpa [blocks, sideBit] using hM 2
      | simpa [blocks, sideBit] using hM 3
  · apply c.matching_even_full M <;> first
      | simpa [blocks, sideBit] using hM 0
      | simpa [blocks, sideBit] using hM 1
      | simpa [blocks, sideBit] using hM 2
      | simpa [blocks, sideBit] using hM 3

lemma assemble_val (b : Bool) (M : Fin 4 → Finset E)
    (hM : ∀ i, MatchingOn inc (M i) (c.blocks b i)) (hinc : ∀ e, ∃ v, inc e v) :
    (assemble M).val = ∑ i, (M i).val := by
  have hd (i j : Fin 4) (hij : i ≠ j) : Disjoint (M i) (M j) :=
    (hM i).disjoint_edges (hM j) hinc (c.blocks_disjoint b hij)
  have hu : Disjoint (M 0 ∪ M 2) (M 1 ∪ M 3) := by
    simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
    exact ⟨⟨hd 0 1 (by decide), hd 2 1 (by decide)⟩,
      ⟨hd 0 3 (by decide), hd 2 3 (by decide)⟩⟩
  rw [assemble, union_val_add hu, union_val_add (hd 0 2 (by decide)),
    union_val_add (hd 1 3 (by decide))]
  rw [Fin.sum_univ_four]
  ac_rfl

omit [DecidableEq E] in
lemma pieces_matching (b : Bool) (full inner : Fin 4 → Finset E)
    (hf : ∀ i, sideBit i = b → MatchingOn inc (full i) (c.side i).span)
    (hi : ∀ i, sideBit i ≠ b → MatchingOn inc (inner i) (c.side i).inside) :
    ∀ i, MatchingOn inc (pieces b full inner i) (c.blocks b i) := by
  intro i
  by_cases h : sideBit i = b
  · simpa only [pieces, blocks, ite_eq_left h] using hf i h
  · simpa only [pieces, blocks, ite_eq_right h] using hi i h

def orientationPieces (b : Bool) : Fin 4 → Finset E :=
  pieces b (fun i => (c.side i).through) (fun i => (c.side i).interior)

def switchPieces (b : Bool) : Fin 4 → Finset E :=
  pieces b (fun i => (c.side i).closed (c.chord i)) (fun i => (c.side i).interior)

def repairPieces (b : Bool) (repair : Fin 4 → E) : Fin 4 → Finset E :=
  pieces b (fun i => (c.side i).through) (fun i => (c.side i).repaired (repair i))

def guidePieces (b : Bool) (repair : Fin 4 → E) : Fin 4 → Finset E :=
  pieces b (fun i => (c.side i).closed (c.chord i)) (fun i => (c.side i).repaired (repair i))

def Repairs (b : Bool) (repair : Fin 4 → E) : Prop :=
  ∀ i, sideBit i ≠ b → (c.side i).length ≠ 1 → ∀ v,
    inc (repair i) v ↔ v = (c.side i).vertex 1 ∨ v = (c.side i).vertex ((c.side i).length - 1)

lemma orientation_pieces_matching (b : Bool) :
    ∀ i, MatchingOn inc (c.orientationPieces b i) (c.blocks b i) :=
  c.pieces_matching b _ _ (fun i _ => (c.side i).through_matching)
    (fun i _ => (c.side i).interior_matching)

lemma switch_pieces_matching (b : Bool) :
    ∀ i, MatchingOn inc (c.switchPieces b i) (c.blocks b i) :=
  c.pieces_matching b _ _ (fun i _ => (c.side i).closed_matching _ (c.chord_incidence i))
    (fun i _ => (c.side i).interior_matching)

lemma repair_pieces_matching (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair) :
    ∀ i, MatchingOn inc (c.repairPieces b repair i) (c.blocks b i) :=
  c.pieces_matching b _ _ (fun i _ => (c.side i).through_matching)
    (fun i hi => (c.side i).repaired_matching _ (hr i hi))

lemma guide_pieces_matching (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair) :
    ∀ i, MatchingOn inc (c.guidePieces b repair i) (c.blocks b i) :=
  c.pieces_matching b _ _ (fun i _ => (c.side i).closed_matching _ (c.chord_incidence i))
    (fun i hi => (c.side i).repaired_matching _ (hr i hi))

def orientation (b : Bool) : Finset E := assemble (c.orientationPieces b)

def switched (b : Bool) : Finset E := assemble (c.switchPieces b)

def repaired (b : Bool) (repair : Fin 4 → E) : Finset E := assemble (c.repairPieces b repair)

def guide (b : Bool) (repair : Fin 4 → E) : Finset E := assemble (c.guidePieces b repair)

lemma orientation_matching (b : Bool) : MatchingOn inc (c.orientation b) c.vertices :=
  c.assembled_matching b _ (c.orientation_pieces_matching b)

lemma switched_matching (b : Bool) : MatchingOn inc (c.switched b) c.vertices :=
  c.assembled_matching b _ (c.switch_pieces_matching b)

lemma repaired_matching (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair) :
    MatchingOn inc (c.repaired b repair) c.vertices :=
  c.assembled_matching b _ (c.repair_pieces_matching b repair hr)

lemma guide_matching (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair) :
    MatchingOn inc (c.guide b repair) c.vertices :=
  c.assembled_matching b _ (c.guide_pieces_matching b repair hr)

lemma component_subset_assemble (M : Fin 4 → Finset E) (i : Fin 4) : M i ⊆ assemble M := by
  intro e he
  fin_cases i <;> simp only [assemble, Finset.mem_union]
  · exact Or.inl (Or.inl he)
  · exact Or.inr (Or.inl he)
  · exact Or.inl (Or.inr he)
  · exact Or.inr (Or.inr he)

lemma closed_subset_guide (b : Bool) (repair : Fin 4 → E) (i : Fin 4) (hi : sideBit i = b) :
    (c.side i).closed (c.chord i) ⊆ c.guide b repair := by
  have h := component_subset_assemble (c.guidePieces b repair) i
  simpa only [guidePieces, pieces, ite_eq_left hi, guide] using h

def drops (r : Bool) : Multiset E :=
  ∑ i, if sideBit i = r then 0 else (c.side i).boundary.val

def additions (b r : Bool) (repair : Fin 4 → E) : Multiset E :=
  (∑ i, if sideBit i = b then {c.chord i} else 0) +
    ∑ i, if sideBit i = r then 0 else (c.side i).repairAdded (repair i)

lemma orientation_val (b : Bool) (hinc : ∀ e, ∃ v, inc e v) :
    (c.orientation b).val = ∑ i, (c.orientationPieces b i).val :=
  c.assemble_val b _ (c.orientation_pieces_matching b) hinc

lemma switched_val (b : Bool) (hinc : ∀ e, ∃ v, inc e v) :
    (c.switched b).val = ∑ i, (c.switchPieces b i).val :=
  c.assemble_val b _ (c.switch_pieces_matching b) hinc

lemma repaired_val (r : Bool) (repair : Fin 4 → E) (hr : c.Repairs r repair)
    (hinc : ∀ e, ∃ v, inc e v) :
    (c.repaired r repair).val = ∑ i, (c.repairPieces r repair i).val :=
  c.assemble_val r _ (c.repair_pieces_matching r repair hr) hinc

lemma guide_val (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair)
    (hinc : ∀ e, ∃ v, inc e v) :
    (c.guide b repair).val = ∑ i, (c.guidePieces b repair i).val :=
  c.assemble_val b _ (c.guide_pieces_matching b repair hr) hinc

lemma two_orientation_pieces (i : Fin 4) :
    (c.orientationPieces true i).val + (c.orientationPieces false i).val =
      (c.side i).through.val + (c.side i).interior.val := by
  cases h : sideBit i <;> simp [orientationPieces, pieces, h, add_comm]

lemma switch_piece_val (b : Bool) (i : Fin 4) (hinc : ∀ e, ∃ v, inc e v) :
    (c.switchPieces b i).val = (c.side i).interior.val +
      (if sideBit i = b then {c.chord i} else 0) := by
  by_cases h : sideBit i = b
  · simp only [switchPieces, pieces, ite_eq_left h]
    exact (c.side i).closed_val _ (c.chord_incidence i) hinc
  · simp [switchPieces, pieces, h]

lemma repair_piece_conservation (r : Bool) (repair : Fin 4 → E)
    (hr : c.Repairs r repair) (i : Fin 4) (hinc : ∀ e, ∃ v, inc e v) :
    (c.repairPieces r repair i).val +
        (if sideBit i = r then 0 else (c.side i).boundary.val) =
      (c.side i).through.val +
        (if sideBit i = r then 0 else (c.side i).repairAdded (repair i)) := by
  by_cases h : sideBit i = r
  · simp [repairPieces, pieces, h]
  · simp only [repairPieces, pieces, ite_eq_right h]
    exact (c.side i).repair_conservation _ (hr i h) hinc

lemma switch_conservation (b r : Bool) (repair : Fin 4 → E)
    (hr : c.Repairs r repair) (hinc : ∀ e, ∃ v, inc e v) :
    (c.orientation true).val + (c.orientation false).val + c.additions b r repair =
      (c.switched b).val + (c.repaired r repair).val + c.drops r := by
  rw [c.orientation_val true hinc, c.orientation_val false hinc,
    c.switched_val b hinc, c.repaired_val r repair hr hinc]
  simp only [additions, drops, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [c.two_orientation_pieces i, c.switch_piece_val b i hinc]
  have h := c.repair_piece_conservation r repair hr i hinc
  calc
    _ = (c.side i).interior.val + (if sideBit i = b then {c.chord i} else 0) +
        ((c.side i).through.val +
          (if sideBit i = r then 0 else (c.side i).repairAdded (repair i))) := by ac_rfl
    _ = _ := by rw [← h]; ac_rfl

lemma guide_piece_conservation (b : Bool) (repair : Fin 4 → E)
    (hr : c.Repairs b repair) (i : Fin 4) (hinc : ∀ e, ∃ v, inc e v) :
    (c.orientationPieces b i).val + (c.guidePieces b repair i).val +
        (if sideBit i = b then 0 else (c.side i).boundary.val) =
      (c.side i).through.val + (c.side i).interior.val +
        (if sideBit i = b then {c.chord i} else 0) +
        (if sideBit i = b then 0 else (c.side i).repairAdded (repair i)) := by
  by_cases h : sideBit i = b
  · simp only [orientationPieces, guidePieces, pieces, ite_eq_left h, add_zero]
    rw [(c.side i).closed_val _ (c.chord_incidence i) hinc]
    ac_rfl
  · simp only [orientationPieces, guidePieces, pieces, ite_eq_right h, add_zero]
    have hh := (c.side i).repair_conservation _ (hr i h) hinc
    calc
      _ = (c.side i).interior.val +
          ((c.side i).repaired (repair i)).val + (c.side i).boundary.val := rfl
      _ = _ := by rw [add_assoc, hh]; ac_rfl

lemma guide_conservation (b : Bool) (repair : Fin 4 → E)
    (hr : c.Repairs b repair) (hinc : ∀ e, ∃ v, inc e v) :
    (c.orientation true).val + (c.orientation false).val + c.additions b b repair =
      (c.orientation b).val + (c.guide b repair).val + c.drops b := by
  rw [c.orientation_val true hinc, c.orientation_val false hinc,
    c.orientation_val b hinc, c.guide_val b repair hr hinc]
  simp only [additions, drops, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [c.two_orientation_pieces i]
  have h := c.guide_piece_conservation b repair hr i hinc
  simpa only [add_assoc] using h.symm

lemma boundary_card_eq (i : Fin 4) (repair : Fin 4 → E) :
    (c.side i).boundary.card = 1 + ((c.side i).repairAdded (repair i)).card := by
  rw [(c.side i).boundary_card]
  by_cases h : (c.side i).length = 1 <;> simp [OddPath.repairAdded, h]

omit [DecidableEq E] in
lemma additions_card (b r : Bool) (repair : Fin 4 → E) :
    (c.additions b r repair).card = 2 +
      ∑ i, if sideBit i = r then 0 else ((c.side i).repairAdded (repair i)).card := by
  simp only [additions, Multiset.card_add, Multiset.card_sum]
  have h1 : (∑ i : Fin 4, (if sideBit i = b then ({c.chord i} : Multiset E) else 0).card) = 2 := by
    cases b <;> norm_num [Fin.sum_univ_four, sideBit]
  rw [h1]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp

lemma modification_cards (b r : Bool) (repair : Fin 4 → E) :
    (c.drops r).card = (c.additions b r repair).card ∧ (c.drops r).card ≤ 4 := by
  have hd : (c.drops r).card = 2 +
      ∑ i, if sideBit i = r then 0 else ((c.side i).repairAdded (repair i)).card := by
    simp only [drops, Multiset.card_sum]
    have hb := c.boundary_card_eq
    cases r <;> norm_num [Fin.sum_univ_four, sideBit]
    all_goals rw [hb _ repair, hb _ repair]; omega
  refine ⟨hd.trans (c.additions_card b r repair).symm, ?_⟩
  rw [hd]
  have hle (i : Fin 4) : ((c.side i).repairAdded (repair i)).card ≤ 1 := by
    by_cases h : (c.side i).length = 1 <;> simp [OddPath.repairAdded, h]
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  cases r <;> norm_num [Fin.sum_univ_four, sideBit]
  all_goals omega

lemma through_subset_orientation (b : Bool) (i : Fin 4) (hi : sideBit i = b) :
    (c.side i).through ⊆ c.orientation b := by
  have h := component_subset_assemble (c.orientationPieces b) i
  simpa only [orientationPieces, pieces, ite_eq_left hi, orientation] using h

omit [DecidableEq E] in
lemma span_subset_vertices (i : Fin 4) : (c.side i).span ⊆ c.vertices := by
  rw [← (c.side i).inside_union_ends, c.ends_eq]
  intro v hv
  fin_cases i <;> simp only [vertices, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hv ⊢ <;> tauto

def contextOne (b : Bool) (Y : Fin 4) : Finset E :=
  (c.orientation b \ (c.side Y).through) ∪ (c.side Y).closed (c.chord Y)

def guideOne (b : Bool) (repair : Fin 4 → E) (Y : Fin 4) : Finset E :=
  (c.guide b repair \ (c.side Y).closed (c.chord Y)) ∪ (c.side Y).through

lemma context_one_properties (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair)
    (Y : Fin 4) (hY : sideBit Y = b) (hinc : ∀ e, ∃ v, inc e v) :
    MatchingOn inc (c.contextOne b Y) c.vertices ∧
    MatchingOn inc (c.guideOne b repair Y) c.vertices ∧
    (c.contextOne b Y).val + (c.guideOne b repair Y).val =
      (c.orientation b).val + (c.guide b repair).val := by
  exact pattern_interchange inc (c.orientation_matching b) (c.guide_matching b repair hr)
    (c.side Y).through_matching ((c.side Y).closed_matching _ (c.chord_incidence Y))
    (c.through_subset_orientation b Y hY) (c.closed_subset_guide b repair Y hY)
    (c.span_subset_vertices Y) hinc

lemma closed_subset_guide_one (b : Bool) (repair : Fin 4 → E) (X Y : Fin 4)
    (hX : sideBit X = b) (hY : sideBit Y = b) (hXY : X ≠ Y)
    (hinc : ∀ e, ∃ v, inc e v) :
    (c.side X).closed (c.chord X) ⊆ c.guideOne b repair Y := by
  have hdis := ((c.side X).closed_matching _ (c.chord_incidence X)).disjoint_edges
    ((c.side Y).closed_matching _ (c.chord_incidence Y)) hinc
    (c.same_bit_spans X Y hXY (hX.trans hY.symm))
  intro e he
  exact Finset.mem_union_left _ <| Finset.mem_sdiff.mpr
    ⟨c.closed_subset_guide b repair X hX he, fun hh => Finset.disjoint_left.mp hdis he hh⟩

lemma context_one_conservation (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair)
    (Y : Fin 4) (hY : sideBit Y = b) (hinc : ∀ e, ∃ v, inc e v) :
    (c.orientation true).val + (c.orientation false).val + c.additions b b repair =
      (c.contextOne b Y).val + (c.guideOne b repair Y).val + c.drops b := by
  rw [(c.context_one_properties b repair hr Y hY hinc).2.2]
  exact c.guide_conservation b repair hr hinc

lemma switch_weight_bound (b r : Bool) (repair : Fin 4 → E) (hr : c.Repairs r repair)
    (hinc : ∀ e, ∃ v, inc e v) (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hcompare : ∀ e ∈ c.drops r, ∀ f ∈ c.additions b r repair, w e ≤ A₀ * w f) :
    (∏ e ∈ c.orientation true, w e) * (∏ e ∈ c.orientation false, w e) ≤
      A₀ ^ 4 * ((∏ e ∈ c.switched b, w e) * ∏ e ∈ c.repaired r repair, w e) := by
  have h := four_edge_weight_bound w hw A₀ hA₀
    ((c.orientation true).val + (c.orientation false).val)
    ((c.switched b).val + (c.repaired r repair).val)
    (c.drops r) (c.additions b r repair) (c.switch_conservation b r repair hr hinc)
    (c.modification_cards b r repair).1 (c.modification_cards b r repair).2 hcompare
  simpa only [Multiset.map_add, Multiset.prod_add, ← Finset.prod_eq_multiset_prod] using h

lemma guide_weight_bound (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair)
    (hinc : ∀ e, ∃ v, inc e v) (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hcompare : ∀ e ∈ c.drops b, ∀ f ∈ c.additions b b repair, w e ≤ A₀ * w f) :
    (∏ e ∈ c.orientation true, w e) * (∏ e ∈ c.orientation false, w e) ≤
      A₀ ^ 4 * ((∏ e ∈ c.orientation b, w e) * ∏ e ∈ c.guide b repair, w e) := by
  have h := four_edge_weight_bound w hw A₀ hA₀
    ((c.orientation true).val + (c.orientation false).val)
    ((c.orientation b).val + (c.guide b repair).val)
    (c.drops b) (c.additions b b repair) (c.guide_conservation b repair hr hinc)
    (c.modification_cards b b repair).1 (c.modification_cards b b repair).2 hcompare
  simpa only [Multiset.map_add, Multiset.prod_add, ← Finset.prod_eq_multiset_prod] using h

lemma context_one_weight_bound (b : Bool) (repair : Fin 4 → E) (hr : c.Repairs b repair)
    (Y : Fin 4) (hY : sideBit Y = b) (hinc : ∀ e, ∃ v, inc e v)
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hcompare : ∀ e ∈ c.drops b, ∀ f ∈ c.additions b b repair, w e ≤ A₀ * w f) :
    (∏ e ∈ c.orientation true, w e) * (∏ e ∈ c.orientation false, w e) ≤
      A₀ ^ 4 * ((∏ e ∈ c.contextOne b Y, w e) * ∏ e ∈ c.guideOne b repair Y, w e) := by
  have h := four_edge_weight_bound w hw A₀ hA₀
    ((c.orientation true).val + (c.orientation false).val)
    ((c.contextOne b Y).val + (c.guideOne b repair Y).val)
    (c.drops b) (c.additions b b repair) (c.context_one_conservation b repair hr Y hY hinc)
    (c.modification_cards b b repair).1 (c.modification_cards b b repair).2 hcompare
  simpa only [Multiset.map_add, Multiset.prod_add, ← Finset.prod_eq_multiset_prod] using h

end CellPaths

end MatchingFPRAS.Transport

end OAI
