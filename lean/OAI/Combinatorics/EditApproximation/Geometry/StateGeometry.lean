import OAI.Combinatorics.EditApproximation.Geometry.Connections
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# The finite domain of valid target states

The endpoint domain is enumerated by actual bounded natural loops. A
state's true cost and signed length gap use the stored target substring.
-/

namespace EditApproximation

open EditDistortion





theorem targetStates_complete (n : ℕ) (q : TargetInterval n) : q ∈ targetStates n := by
  apply List.mem_flatMap.mpr
  refine ⟨q.lo, List.mem_range.mpr (Nat.lt_succ_of_le (q.ordered.trans q.valid)), ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨q.hi, List.mem_range.mpr (Nat.lt_succ_of_le q.valid), ?_⟩
  rw [makeTargetState, dite_eq_left (show q.lo ≤ q.hi ∧ q.hi ≤ n from ⟨q.ordered, q.valid⟩)]



theorem natural_distance_cast (a b : ℕ) : |(a : ℝ) - b| = (Nat.dist a b : ℝ) := by
  rcases le_total a b with h | h
  · have hR : (a : ℝ) ≤ b := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr hR)]
    ring
  · have hR : (b : ℝ) ≤ a := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr hR)]

noncomputable def stateEditCost {α : Type*} (source target : List α) (q : TargetInterval target.length) : ℕ :=
  edit source (substring target q.lo q.hi)

def stateLengthGap {α : Type*} (source target : List α) (q : TargetInterval target.length) : ℝ :=
  (q.hi : ℝ) - q.lo - source.length

theorem stateLengthGap_actual {α : Type*} (source target : List α)
    (q : TargetInterval target.length) :
    stateLengthGap source target q = signedLengthGap source (substring target q.lo q.hi) := by
  have hlength : (substring target q.lo q.hi).length = q.hi - q.lo := by
    simp only [substring, List.length_drop, List.length_take, Nat.min_eq_left q.valid]
  unfold stateLengthGap signedLengthGap
  rw [hlength, Nat.cast_sub q.ordered]

theorem stateEditCost_length_lower {α : Type*} (source target : List α)
    (q : TargetInterval target.length) :
    |stateLengthGap source target q| ≤ stateEditCost source target q := by
  rw [stateLengthGap_actual]
  exact abs_length_gap_le_edit source (substring target q.lo q.hi)

theorem stateEditCost_spatial {α : Type*} (source target : List α)
    (q r : TargetInterval target.length) :
    stateEditCost source target q ≤ stateEditCost source target r + targetEndpointDistance q r := by
  have hmove := edit_substring_endpoints_le target r.lo r.hi q.lo q.hi
  have htriangle := cost_triangle (s := true) source
    (substring target r.lo r.hi) (substring target q.lo q.hi)
  change edit source (substring target q.lo q.hi) ≤
    edit source (substring target r.lo r.hi) + edit (substring target r.lo r.hi) (substring target q.lo q.hi)
    at htriangle
  change edit source (substring target q.lo q.hi) ≤
    edit source (substring target r.lo r.hi) + (Nat.dist q.lo r.lo + Nat.dist q.hi r.hi)
  rw [Nat.dist_comm r.lo q.lo, Nat.dist_comm r.hi q.hi] at hmove
  omega

theorem stateLengthGap_spatial {α : Type*} (source target : List α)
    (q r : TargetInterval target.length) :
    |stateLengthGap source target q| ≤ |stateLengthGap source target r| + targetEndpointDistance q r := by
  have hlo : |(q.lo : ℝ) - r.lo| = Nat.dist q.lo r.lo := by
    exact natural_distance_cast q.lo r.lo
  have hhi : |(q.hi : ℝ) - r.hi| = Nat.dist q.hi r.hi := by
    exact natural_distance_cast q.hi r.hi
  have hdiff : stateLengthGap source target q - stateLengthGap source target r =
      ((q.hi : ℝ) - r.hi) - ((q.lo : ℝ) - r.lo) := by unfold stateLengthGap; ring
  have hmetric : |stateLengthGap source target q - stateLengthGap source target r| ≤
      (targetEndpointDistance q r : ℝ) := by
    rw [hdiff]
    have habs := abs_sub ((q.hi : ℝ) - r.hi) ((q.lo : ℝ) - r.lo)
    rw [hhi, hlo] at habs
    simpa only [targetEndpointDistance, Nat.cast_add, add_comm] using habs
  have h := (abs_sub_abs_le_abs_sub _ _).trans hmetric
  linarith

end EditApproximation

end OAI
