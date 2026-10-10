import OAI.Combinatorics.EditApproximation.Geometry.LocalGrid
import OAI.Combinatorics.EditApproximation.Geometry.InitialConeGrid
import OAI.Combinatorics.EditApproximation.Probability.FiniteAssignments
import OAI.Combinatorics.EditApproximation.Geometry.BalancedIntervals
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Executable wide action lists

Endpoint indices are generated in the radius-`10b` grid boxes anchored
at the physical source cuts. Lists contain exactly the valid grid states
in those boxes and their Cartesian product over labeled children.
-/

namespace EditApproximation



theorem gridStateBox_complete {n g radius lo hi : ℕ} (hg : 0 < g)
    (r : TargetInterval n) (hlo : Nat.dist lo r.lo ≤ radius)
    (hhi : Nat.dist hi r.hi ≤ radius) (hgrid : g ∣ r.lo ∧ g ∣ r.hi) :
    r ∈ gridStateBox n g radius lo hi := by
  have hlo' : lo - radius ≤ r.lo ∧ r.lo ≤ lo + radius := by unfold Nat.dist at hlo; omega
  have hhi' : hi - radius ≤ r.hi ∧ r.hi ≤ hi + radius := by unfold Nat.dist at hhi; omega
  apply List.mem_flatMap.mpr
  refine ⟨r.lo, gridPointsBetween_complete hg hlo'.1 hlo'.2 hgrid.1, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨r.hi, gridPointsBetween_complete hg hhi'.1 hhi'.2 hgrid.2, ?_⟩
  rw [makeTargetState, dite_eq_left (show r.lo ≤ r.hi ∧ r.hi ≤ n from ⟨r.ordered, r.valid⟩)]

theorem gridStateBox_length_le (n g radius lo hi : ℕ) (hg : 0 < g) :
    (gridStateBox n g radius lo hi).length ≤ (2 * radius / g + 2) ^ 2 := by
  have hpoint (p : ℕ) :
      (gridPointsBetween g (p - radius) (p + radius)).length ≤ 2 * radius / g + 2 := by
    have hlength := gridPointsBetween_length_le g (p - radius) (p + radius) hg
    have hwidth : p + radius - (p - radius) ≤ 2 * radius := by omega
    exact hlength.trans (Nat.add_le_add_right (Nat.div_le_div_right hwidth) 2)
  have hlist := list_flatMap_length_le
    (gridPointsBetween g (lo - radius) (lo + radius))
    (fun s => (gridPointsBetween g (hi - radius) (hi + radius)).filterMap
      fun t => makeTargetState n s t)
    (2 * radius / g + 2) (by intro s hs; exact (List.length_filterMap_le _ _).trans (hpoint hi))
  exact hlist.trans (by simpa only [pow_two] using
    (Nat.mul_le_mul_right (2 * radius / g + 2) (hpoint lo)))





theorem wideActionList_complete {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (action : Fin M → TargetInterval ny)
    (hgrid : ∀ i, seedGridSpacing b P ∣ (action i).lo ∧ seedGridSpacing b P ∣ (action i).hi)
    (hlo : ∀ i, Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (action i).lo ≤ 10 * b)
    (hhi : ∀ i, Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (action i).hi ≤ 10 * b) :
    action ∈ wideActionList M parent r b P := by
  apply finiteAssignments_complete
  intro i
  exact gridStateBox_complete (by unfold seedGridSpacing; omega) (action i)
    (hlo i) (hhi i) (hgrid i)

theorem seedGridSpacing_radius_count (b P : ℕ) (hP : 0 < P) :
    20 * b / seedGridSpacing b P + 2 ≤ 40 * P + 2 := by
  let g := seedGridSpacing b P
  have hg : 0 < g := by unfold g seedGridSpacing; omega
  have hg1 : 1 ≤ g := hg
  have hquot : b / P ≤ g := le_max_right _ _
  have hdiv := Nat.lt_mul_div_succ b hP
  have hprod : b < 2 * P * g := by nlinarith
  have hscale : 20 * b < (40 * P + 1) * g := by nlinarith
  have hresult := (Nat.div_lt_iff_lt_mul hg).2 hscale
  change 20 * b / g + 2 ≤ 40 * P + 2
  omega

theorem wideActionList_length_le {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hP : 0 < P) :
    (wideActionList M parent r b P).length ≤ (40 * P + 2) ^ (2 * M) := by
  have hchoices (i : Fin M) : (wideChildStateList parent r b P i).length ≤ (40 * P + 2) ^ 2 := by
    have hlocal := gridStateBox_length_le ny (seedGridSpacing b P) (10 * b)
      (r.lo + ((sourceChild parent i).lo - parent.lo))
      (r.lo + ((sourceChild parent i).hi - parent.lo))
      (by unfold seedGridSpacing; omega)
    have hcount := seedGridSpacing_radius_count b P hP
    apply hlocal.trans
    apply Nat.pow_le_pow_left
    simpa only [show 2 * (10 * b) = 20 * b by omega] using hcount
  have h := finiteAssignments_length_le M ((40 * P + 2) ^ 2)
    (wideChildStateList parent r b P) hchoices
  simpa only [wideActionList, ← pow_mul] using h

end EditApproximation

end OAI
