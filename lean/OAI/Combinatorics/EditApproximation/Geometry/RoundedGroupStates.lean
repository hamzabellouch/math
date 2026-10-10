import OAI.Combinatorics.EditApproximation.Geometry.GroupSamplingWork
import OAI.Combinatorics.EditApproximation.Geometry.WideActions
import OAI.Combinatorics.EditApproximation.Geometry.GroupCells
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Enumerating rounded endpoints with a length-gap guard costs only
one wide coordinate and one envelope coordinate. -/

namespace EditApproximation



theorem gridGapStates_complete {n g anchor radius sourceLength gapRadius : ℕ}
    (hg : 0 < g) (r : TargetInterval n)
    (hfirst : Nat.dist anchor r.lo ≤ radius)
    (hgap : Nat.dist (r.lo + sourceLength) r.hi ≤ gapRadius)
    (hgrid : g ∣ r.lo ∧ g ∣ r.hi) :
    r ∈ gridGapStates n g anchor radius sourceLength gapRadius := by
  have hlo : anchor - radius ≤ r.lo ∧ r.lo ≤ anchor + radius := by unfold Nat.dist at hfirst; omega
  have hhi : r.lo + sourceLength - gapRadius ≤ r.hi ∧ r.hi ≤ r.lo + sourceLength + gapRadius := by
    unfold Nat.dist at hgap
    omega
  apply List.mem_flatMap.mpr
  refine ⟨r.lo, gridPointsBetween_complete hg hlo.1 hlo.2 hgrid.1, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨r.hi, gridPointsBetween_complete hg hhi.1 hhi.2 hgrid.2, ?_⟩
  rw [makeTargetState, dite_eq_left (show r.lo ≤ r.hi ∧ r.hi ≤ n from ⟨r.ordered, r.valid⟩)]

theorem gridGapStates_length_le (n g anchor radius sourceLength gapRadius : ℕ) (hg : 0 < g) :
    (gridGapStates n g anchor radius sourceLength gapRadius).length ≤
      (2 * radius / g + 2) * (2 * gapRadius / g + 2) := by
  have hpoint (p rad : ℕ) : (gridPointsBetween g (p - rad) (p + rad)).length ≤ 2 * rad / g + 2 := by
    exact (gridPointsBetween_length_le g _ _ hg).trans
      (Nat.add_le_add_right (Nat.div_le_div_right (by omega : p + rad - (p - rad) ≤ 2 * rad)) 2)
  have h := list_flatMap_length_le (gridPointsBetween g (anchor - radius) (anchor + radius))
    (fun lo => (gridPointsBetween g (lo + sourceLength - gapRadius) (lo + sourceLength + gapRadius)).filterMap
      fun hi => makeTargetState n lo hi) (2 * gapRadius / g + 2)
    (fun lo _ => (List.length_filterMap_le _ _).trans (hpoint (lo + sourceLength) gapRadius))
  exact h.trans (Nat.mul_le_mul_right _ (hpoint anchor radius))

theorem lengthGap_guard_distance {n : ℕ} (r : TargetInterval n) (sourceLength : ℕ) (h : ℚ)
    (hguard : |(r.hi : ℚ) - r.lo - sourceLength| ≤ 2 * h) :
    Nat.dist (r.lo + sourceLength) r.hi ≤ ⌈2 * h⌉₊ := by
  have hcast : (Nat.dist (r.lo + sourceLength) r.hi : ℚ) =
      |(r.hi : ℚ) - r.lo - sourceLength| := by
    have hd : |((r.lo + sourceLength : ℕ) : ℚ) - r.hi| =
        (Nat.dist (r.lo + sourceLength) r.hi : ℚ) := by
      exact_mod_cast natural_distance_cast (r.lo + sourceLength) r.hi
    rw [← hd, abs_sub_comm]
    congr 1
    push_cast
    ring
  have hbound : (Nat.dist (r.lo + sourceLength) r.hi : ℚ) ≤ (⌈2 * h⌉₊ : ℚ) :=
    hcast.le.trans (hguard.trans (Nat.le_ceil _))
  exact_mod_cast hbound

theorem wide_firstEndpoint_near_cell {n g b : ℕ} {theta : ℚ}
    (cell : ℕ × ℕ) (hg : 0 < g) (htheta : 0 ≤ theta ∧ theta ≤ 1) (hb : 1 ≤ b)
    (center r : TargetInterval n) (offset : ℕ)
    (hcenter : center ∈ cellTargetStates n g (theta * b) cell)
    (hwide : Nat.dist (center.lo + offset) r.lo ≤ 10 * b) :
    Nat.dist (⌊(cell.1 : ℚ) * (theta * b)⌋₊ + offset) r.lo ≤ 12 * b := by
  have hc := (cellTargetStates_mem cell hg center).mp hcenter
  have hbase : 0 ≤ (cell.1 : ℚ) * (theta * b) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg htheta.1 (Nat.cast_nonneg _))
  have hfloor := Nat.floor_le hbase
  have hfloorUpper := Nat.lt_floor_add_one ((cell.1 : ℚ) * (theta * b))
  have hthetaB := mul_le_mul_of_nonneg_right htheta.2 (Nat.cast_nonneg (α := ℚ) b)
  have hbR : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have hlo : ⌊(cell.1 : ℚ) * (theta * b)⌋₊ ≤ center.lo := by
    exact_mod_cast hfloor.trans hc.2.2.1
  have hhi : center.lo ≤ ⌊(cell.1 : ℚ) * (theta * b)⌋₊ + 2 * b := by
    have hhiR : (center.lo : ℚ) ≤ (⌊(cell.1 : ℚ) * (theta * b)⌋₊ : ℚ) + 2 * b := by
      nlinarith only [hc.2.2.2.1, hfloorUpper, hthetaB, hbR]
    exact_mod_cast hhiR
  unfold Nat.dist at hwide ⊢
  omega

/-- The spacing dominates h/K and one. This includes the spacing-one
case for fractional envelopes. No success or accuracy event is needed. -/
theorem gridGapStates_rounded_count (n g anchor sourceLength b : ℕ) (h K : ℚ)
    (hg : 0 < g) (hh : 0 < h) (hK : 1 ≤ K) (hspacing : h ≤ K * g) :
    ((gridGapStates n g anchor (12 * b) sourceLength ⌈2 * h⌉₊).length : ℚ) ≤
      208 * K ^ 2 * (1 + b / h) := by
  have hgr : (0 : ℚ) < g := by exact_mod_cast hg
  have hg1 : (1 : ℚ) ≤ g := by exact_mod_cast hg
  have hKr : 0 ≤ K := le_trans zero_le_one hK
  have hb : (0 : ℚ) ≤ b := Nat.cast_nonneg _
  have hfirstDiv : ((24 * b / g : ℕ) : ℚ) ≤ 24 * K * b / h := by
    apply (Nat.cast_div_le (m := 24 * b) (n := g)).trans
    push_cast
    apply (div_le_div_iff₀ hgr hh).2
    have hm := mul_le_mul_of_nonneg_right hspacing (show (0 : ℚ) ≤ 24 * b by positivity)
    nlinarith only [hm]
  have hceil : (⌈2 * h⌉₊ : ℚ) < 2 * h + 1 := Nat.ceil_lt_add_one (by positivity)
  have hsecondDiv : ((2 * ⌈2 * h⌉₊ / g : ℕ) : ℚ) ≤ 4 * K + 2 := by
    apply (Nat.cast_div_le (m := 2 * ⌈2 * h⌉₊) (n := g)).trans
    push_cast
    apply (div_le_iff₀ hgr).2
    nlinarith only [hceil, hspacing, hg1]
  have hratio : 0 ≤ (b : ℚ) / h := div_nonneg hb hh.le
  have hfirst : (((2 * (12 * b) / g + 2 : ℕ) : ℚ)) ≤ 26 * K * (1 + b / h) := by
    have heq : 2 * (12 * b) = 24 * b := by omega
    rw [heq, Nat.cast_add, Nat.cast_ofNat]
    have hquotient : 24 * K * b / h = 24 * K * (b / h) := by ring
    rw [hquotient] at hfirstDiv
    have hKr' := mul_nonneg hKr hratio
    nlinarith only [hfirstDiv, hK, hKr']
  have hsecond : (((2 * ⌈2 * h⌉₊ / g + 2 : ℕ) : ℚ)) ≤ 8 * K := by
    rw [Nat.cast_add, Nat.cast_ofNat]
    linarith only [hsecondDiv, hK]
  have hlength : ((gridGapStates n g anchor (12 * b) sourceLength ⌈2 * h⌉₊).length : ℚ) ≤
      (((2 * (12 * b) / g + 2 : ℕ) : ℚ)) * (((2 * ⌈2 * h⌉₊ / g + 2 : ℕ) : ℚ)) := by
    exact_mod_cast gridGapStates_length_le n g anchor (12 * b) sourceLength ⌈2 * h⌉₊ hg
  apply hlength.trans
  calc
    _ ≤ (26 * K * (1 + b / h)) * (8 * K) :=
      mul_le_mul hfirst hsecond (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

theorem shared_rounded_inputs_bound {M Q b : ℕ} {h K states : ℚ}
    (hM : 0 < M) (hQ : 1 ≤ Q) (hb : 0 < b) (hh : 0 < h)
    (hfloor : (b : ℚ) / M ≤ h) (hstates : states ≤ 208 * K ^ 2 * (1 + b / h)) :
    (groupSampleCount M Q b h : ℚ) * states ≤ 624 * M * Q * K ^ 2 := by
  have hwork := groupSampleCount_shared_work hM hQ hb hh hfloor
  have hstateBound := mul_le_mul_of_nonneg_left hstates
    (Nat.cast_nonneg (α := ℚ) (groupSampleCount M Q b h))
  have hworkBound := mul_le_mul_of_nonneg_left hwork (by positivity : (0 : ℚ) ≤ 208 * K ^ 2)
  nlinarith only [hstateBound, hworkBound]

end EditApproximation

end OAI
