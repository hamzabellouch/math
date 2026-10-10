import OAI.Combinatorics.EditApproximation.Geometry.LocalGrid
import OAI.Combinatorics.EditApproximation.Geometry.ActualRepresentatives
import OAI.Combinatorics.EditApproximation.Geometry.BandRounding
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Whole rational cells are enumerated by bounded ranges of grid indices. -/

namespace EditApproximation



theorem cellGridPoints_mem {side : ℚ} {g cell p : ℕ} (hg : 0 < g) :
    p ∈ cellGridPoints side g cell ↔
      g ∣ p ∧ (cell : ℚ) * side ≤ p ∧ (p : ℚ) < ((cell : ℚ) + 1) * side := by
  have hgr : (0 : ℚ) < g := by exact_mod_cast hg
  constructor
  · intro hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hi
    have hlo : ⌈(cell : ℚ) * side / g⌉₊ ≤ ⌈(cell : ℚ) * side / g⌉₊ + 1 * j := by omega
    have hhi : ⌈(cell : ℚ) * side / g⌉₊ + 1 * j < ⌈((cell : ℚ) + 1) * side / g⌉₊ := by omega
    have hloR := (Nat.ceil_le.mp hlo)
    have hhiR := (Nat.lt_ceil.mp hhi)
    refine ⟨dvd_mul_right _ _, ?_, ?_⟩
    · have h := (div_le_iff₀ hgr).mp hloR
      push_cast at h
      push_cast
      simpa only [mul_comm] using h
    · have h := (lt_div_iff₀ hgr).mp hhiR
      push_cast at h
      push_cast
      simpa only [mul_comm] using h
  · rintro ⟨hgrid, hlo, hhi⟩
    have heq : g * (p / g) = p := Nat.mul_div_cancel' hgrid
    have hloR : (cell : ℚ) * side / g ≤ (p / g : ℕ) := by
      apply (div_le_iff₀ hgr).2
      have hc : (g : ℚ) * (p / g : ℕ) = p := by exact_mod_cast heq
      linarith only [hlo, hc]
    have hhiR : ((p / g : ℕ) : ℚ) < ((cell : ℚ) + 1) * side / g := by
      apply (lt_div_iff₀ hgr).2
      have hc : (g : ℚ) * (p / g : ℕ) = p := by exact_mod_cast heq
      linarith only [hhi, hc]
    have hstart := Nat.ceil_le.mpr hloR
    have hend := Nat.lt_ceil.mpr hhiR
    apply List.mem_map.mpr
    refine ⟨p / g, List.mem_range'.mpr ?_, heq⟩
    exact ⟨p / g - ⌈(cell : ℚ) * side / g⌉₊, by omega, by omega⟩

theorem cellGridPoints_length_le {side : ℚ} {g cell P : ℕ}
    (hside : 0 ≤ side) (hsize : side / g ≤ P) :
    (cellGridPoints side g cell).length ≤ P := by
  have hbase : 0 ≤ (cell : ℚ) * side / g :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hside) (Nat.cast_nonneg _)
  have hupper : ((cell : ℚ) + 1) * side / g ≤ (cell : ℚ) * side / g + P := by
    calc
      _ = (cell : ℚ) * side / g + side / g := by ring
      _ ≤ _ := add_le_add_right hsize _
  have hceil := Nat.ceil_le_ceil hupper
  rw [Nat.ceil_add_natCast hbase P] at hceil
  simp only [cellGridPoints, List.length_map, List.length_range']
  omega



theorem cellTargetStates_mem {n g : ℕ} {side : ℚ} (cell : ℕ × ℕ) (hg : 0 < g)
    (q : TargetInterval n) :
    q ∈ cellTargetStates n g side cell ↔
      g ∣ q.lo ∧ g ∣ q.hi ∧
      (cell.1 : ℚ) * side ≤ q.lo ∧ (q.lo : ℚ) < ((cell.1 : ℚ) + 1) * side ∧
      (cell.2 : ℚ) * side ≤ q.hi ∧ (q.hi : ℚ) < ((cell.2 : ℚ) + 1) * side := by
  constructor
  · intro hq
    obtain ⟨lo, hlo, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨hi, hhi, hq⟩ := List.mem_filterMap.mp hq
    have hstate : q.lo = lo ∧ q.hi = hi := by
      unfold makeTargetState at hq
      split_ifs at hq with hvalid
      have heq := Option.some.inj hq
      exact ⟨congrArg TargetInterval.lo heq.symm, congrArg TargetInterval.hi heq.symm⟩
    rw [← hstate.1] at hlo
    rw [← hstate.2] at hhi
    have hl := cellGridPoints_mem hg |>.mp hlo
    have hh := cellGridPoints_mem hg |>.mp hhi
    exact ⟨hl.1, hh.1, hl.2.1, hl.2.2, hh.2.1, hh.2.2⟩
  · rintro ⟨hlo, hhi, hloL, hloU, hhiL, hhiU⟩
    apply List.mem_flatMap.mpr
    refine ⟨q.lo, (cellGridPoints_mem hg).mpr ⟨hlo, hloL, hloU⟩, List.mem_filterMap.mpr ?_⟩
    refine ⟨q.hi, (cellGridPoints_mem hg).mpr ⟨hhi, hhiL, hhiU⟩, ?_⟩
    rw [makeTargetState, dite_eq_left (show q.lo ≤ q.hi ∧ q.hi ≤ n from ⟨q.ordered, q.valid⟩)]

theorem cellTargetStates_length_le {n g P : ℕ} {side : ℚ} (cell : ℕ × ℕ)
    (hside : 0 ≤ side) (hsize : side / g ≤ P) :
    (cellTargetStates n g side cell).length ≤ P ^ 2 := by
  have hfirst := cellGridPoints_length_le (cell := cell.1) hside hsize
  have hsecond := cellGridPoints_length_le (cell := cell.2) hside hsize
  have h := list_flatMap_length_le (cellGridPoints side g cell.1)
    (fun lo => (cellGridPoints side g cell.2).filterMap fun hi => makeTargetState n lo hi) P
    (fun lo _ => (List.length_filterMap_le _ _).trans hsecond)
  exact h.trans (by simpa only [pow_two] using Nat.mul_le_mul_right P hfirst)

theorem cellTargetStates_diameter {n g : ℕ} {side : ℚ} (cell : ℕ × ℕ) (hg : 0 < g)
    (q r : TargetInterval n) (hq : q ∈ cellTargetStates n g side cell)
    (hr : r ∈ cellTargetStates n g side cell) : (targetEndpointDistance q r : ℚ) ≤ 2 * side := by
  have hq' := (cellTargetStates_mem cell hg q).mp hq
  have hr' := (cellTargetStates_mem cell hg r).mp hr
  have hlo : |(q.lo : ℚ) - r.lo| ≤ side := by
    apply abs_le.mpr
    constructor <;> linarith only [hq'.2.2.1, hq'.2.2.2.1, hr'.2.2.1, hr'.2.2.2.1]
  have hhi : |(q.hi : ℚ) - r.hi| ≤ side := by
    apply abs_le.mpr
    constructor <;> linarith only [hq'.2.2.2.2.1, hq'.2.2.2.2.2, hr'.2.2.2.2.1, hr'.2.2.2.2.2]
  have hcast (a b : ℕ) : |(a : ℚ) - b| = (Nat.dist a b : ℚ) := by
    exact_mod_cast natural_distance_cast a b
  rw [targetEndpointDistance, Nat.cast_add, ← hcast, ← hcast]
  linarith only [hlo, hhi]

theorem seedGridSpacing_covers_dyadic {b P : ℕ}
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    b ≤ P * seedGridSpacing b P := by
  obtain ⟨eb, rfl⟩ := hb
  obtain ⟨eP, rfl⟩ := hP
  by_cases horder : eP ≤ eb
  · rw [seedGridSpacing, Nat.pow_div horder (by decide : 0 < 2), max_eq_right Nat.one_le_two_pow,
      ← pow_add, Nat.add_sub_of_le horder]
  · have hle : 2 ^ eb ≤ 2 ^ eP := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    exact hle.trans (Nat.le_mul_of_pos_right _ (by unfold seedGridSpacing; omega))

def targetCell {n : ℕ} (side : ℚ) (q : TargetInterval n) : ℕ × ℕ :=
  (⌊(q.lo : ℚ) / side⌋₊, ⌊(q.hi : ℚ) / side⌋₊)

theorem targetCell_contains {n g : ℕ} {side : ℚ} (hg : 0 < g) (hside : 0 < side)
    (q : TargetInterval n) (hgrid : g ∣ q.lo ∧ g ∣ q.hi) :
    q ∈ cellTargetStates n g side (targetCell side q) := by
  have hcoordinate (p : ℕ) : (⌊(p : ℚ) / side⌋₊ : ℚ) * side ≤ p ∧
      (p : ℚ) < ((⌊(p : ℚ) / side⌋₊ : ℚ) + 1) * side := by
    exact ⟨(le_div_iff₀ hside).mp (Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hside.le)),
      (div_lt_iff₀ hside).mp (Nat.lt_floor_add_one ((p : ℚ) / side))⟩
  exact (cellTargetStates_mem _ hg q).mpr
    ⟨hgrid.1, hgrid.2, (hcoordinate q.lo).1, (hcoordinate q.lo).2,
      (hcoordinate q.hi).1, (hcoordinate q.hi).2⟩



theorem cellRepresentativeStates_mem_representatives {n N P F b : ℕ}
    (a : ℚ) (initial : TargetInterval n → ℚ) (theta : ℚ) (cell : ℕ × ℕ)
    (r : TargetInterval n) (hb : b ∈ dyadicScales N)
    (hr : r ∈ cellRepresentativeStates n P F b a initial theta cell) :
    (b, r) ∈ representativeList N P F a initial := by
  obtain ⟨hcell, heligible⟩ := List.mem_filter.mp hr
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hgrid := (cellTargetStates_mem cell hg r).mp hcell
  exact representativeList_mem a initial r hb ⟨hgrid.1, hgrid.2.1⟩
    (of_decide_eq_true heligible).1 (of_decide_eq_true heligible).2

theorem cellRepresentativeStates_length_le {n P F b : ℕ}
    (a : ℚ) (initial : TargetInterval n → ℚ) (theta : ℚ) (cell : ℕ × ℕ)
    (htheta : 0 ≤ theta ∧ theta ≤ 1)
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    (cellRepresentativeStates n P F b a initial theta cell).length ≤ (P + 1) ^ 2 := by
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hgr : (0 : ℚ) < seedGridSpacing b P := by exact_mod_cast hg
  have hcover : (b : ℚ) ≤ P * (seedGridSpacing b P : ℚ) := by
    exact_mod_cast seedGridSpacing_covers_dyadic hb hP
  have hsize : theta * b / seedGridSpacing b P ≤ (P : ℚ) := by
    apply (div_le_iff₀ hgr).2
    have h := mul_le_mul_of_nonneg_right htheta.2 (Nat.cast_nonneg (α := ℚ) b)
    simp only [one_mul] at h
    exact h.trans hcover
  unfold cellRepresentativeStates
  apply (List.length_filter_le _ _).trans
  exact (cellTargetStates_length_le (n := n) cell
    (mul_nonneg htheta.1 (Nat.cast_nonneg _)) hsize).trans
      (Nat.pow_le_pow_left (Nat.le_succ P) 2)

theorem cellRepresentativeStates_contains {n P F b : ℕ}
    (a : ℚ) (initial : TargetInterval n → ℚ) (theta : ℚ) (r : TargetInterval n)
    (hside : 0 < theta * b) (hgrid : seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi)
    (heligible : (b : ℚ) / (4 * a) ≤ initial r ∧ initial r ≤ 8 * F * b) :
    r ∈ cellRepresentativeStates n P F b a initial theta (targetCell (theta * b) r) := by
  apply List.mem_filter.mpr
  exact ⟨targetCell_contains (by unfold seedGridSpacing; omega) hside r hgrid, decide_eq_true heligible⟩

end EditApproximation

end OAI
