import OAI.Combinatorics.EditApproximation.Geometry.Grid
import OAI.Combinatorics.EditApproximation.Geometry.DomainCounts
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Direct enumeration of a local grid square

The algorithm enumerates bounded ranges of grid indices. It does not
scan the unrelated target positions. The completeness theorem includes
boundary states and intervals with equal endpoints.
-/

namespace EditApproximation



theorem gridPointsBetween_complete {g lo hi p : ℕ} (hg : 0 < g)
    (hlo : lo ≤ p) (hhi : p ≤ hi) (hgrid : g ∣ p) : p ∈ gridPointsBetween g lo hi := by
  have hp : g * (p / g) = p := Nat.mul_div_cancel' hgrid
  have hstart : lo ⌈/⌉ g ≤ p / g := (ceilDiv_le_iff_le_mul hg).2 (by omega)
  have hend : p / g ≤ hi / g := Nat.div_le_div_right hhi
  apply List.mem_map.mpr
  refine ⟨p / g, List.mem_range'.mpr ?_, hp⟩
  refine ⟨p / g - lo ⌈/⌉ g, by omega, ?_⟩
  omega

theorem gridPointsBetween_sound {g lo hi p : ℕ} (hg : 0 < g)
    (hp : p ∈ gridPointsBetween g lo hi) : lo ≤ p ∧ p ≤ hi ∧ g ∣ p := by
  obtain ⟨i, hmem, rfl⟩ := List.mem_map.mp hp
  obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hmem
  have hstart : lo ≤ g * (lo ⌈/⌉ g) := (ceilDiv_le_iff_le_mul hg).mp le_rfl
  have hindex : lo ⌈/⌉ g + 1 * j ≤ hi / g := by omega
  have hfinish := Nat.mul_div_le hi g
  exact ⟨by nlinarith, (Nat.mul_le_mul_left g hindex).trans hfinish, dvd_mul_right _ _⟩

theorem gridPointsBetween_length (g lo hi : ℕ) :
    (gridPointsBetween g lo hi).length = (hi / g + 1) - lo ⌈/⌉ g := by
  simp only [gridPointsBetween, List.length_map, List.length_range']

theorem gridPointsBetween_length_le (g lo hi : ℕ) (hg : 0 < g) :
    (gridPointsBetween g lo hi).length ≤ (hi - lo) / g + 2 := by
  rw [gridPointsBetween_length]
  have hceil : lo ≤ g * (lo ⌈/⌉ g) := (ceilDiv_le_iff_le_mul hg).mp le_rfl
  have hfloor : lo / g ≤ lo ⌈/⌉ g := by
    have hdiv := Nat.div_le_div_right (c := g) hceil
    simpa only [Nat.mul_div_right _ hg] using hdiv
  by_cases horder : lo ≤ hi
  · have hlo := Nat.lt_mul_div_succ lo hg
    have hdiff := Nat.lt_mul_div_succ (hi - lo) hg
    have hsplit : lo + (hi - lo) = hi := Nat.add_sub_of_le horder
    have hdiv : hi / g < lo / g + (hi - lo) / g + 2 := by
      apply (Nat.div_lt_iff_lt_mul hg).2
      nlinarith
    apply Nat.sub_le_of_le_add
    calc
      hi / g + 1 ≤ lo / g + (hi - lo) / g + 2 := hdiv
      _ ≤ (lo ⌈/⌉ g) + (hi - lo) / g + 2 := by gcongr
      _ = (hi - lo) / g + 2 + lo ⌈/⌉ g := by omega
  · have hmono := Nat.div_le_div_right (c := g) (by omega : hi ≤ lo)
    have hshort : hi / g + 1 - lo ⌈/⌉ g ≤ 1 := Nat.sub_le_of_le_add (by omega)
    exact hshort.trans ((by decide : 1 ≤ 2).trans (Nat.le_add_left 2 _))



theorem localTargetStates_complete {n g radius : ℕ} (hg : 0 < g)
    (q r : TargetInterval n) (hlo : Nat.dist q.lo r.lo ≤ radius)
    (hhi : Nat.dist q.hi r.hi ≤ radius) (hgrid : g ∣ r.lo ∧ g ∣ r.hi) :
    r ∈ localTargetStates n g radius q := by
  have hlo' : q.lo - radius ≤ r.lo ∧ r.lo ≤ q.lo + radius := by
    unfold Nat.dist at hlo
    omega
  have hhi' : q.hi - radius ≤ r.hi ∧ r.hi ≤ q.hi + radius := by
    unfold Nat.dist at hhi
    omega
  apply List.mem_flatMap.mpr
  refine ⟨r.lo, gridPointsBetween_complete hg hlo'.1 hlo'.2 hgrid.1, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨r.hi, gridPointsBetween_complete hg hhi'.1 hhi'.2 hgrid.2, ?_⟩
  rw [makeTargetState, dite_eq_left (show r.lo ≤ r.hi ∧ r.hi ≤ n from ⟨r.ordered, r.valid⟩)]

theorem localTargetStates_length_le {n g radius : ℕ} (hg : 0 < g)
    (q : TargetInterval n) :
    (localTargetStates n g radius q).length ≤ (2 * radius / g + 2) ^ 2 := by
  have hpoint (p : ℕ) :
      (gridPointsBetween g (p - radius) (p + radius)).length ≤ 2 * radius / g + 2 := by
    have hlength := gridPointsBetween_length_le g (p - radius) (p + radius) hg
    have hwidth : p + radius - (p - radius) ≤ 2 * radius := by omega
    exact hlength.trans (Nat.add_le_add_right (Nat.div_le_div_right hwidth) 2)
  have hlist := list_flatMap_length_le
    (gridPointsBetween g (q.lo - radius) (q.lo + radius))
    (fun lo => (gridPointsBetween g (q.hi - radius) (q.hi + radius)).filterMap
      fun hi => makeTargetState n lo hi)
    (2 * radius / g + 2) (by
      intro lo hlo
      exact (List.length_filterMap_le _ _).trans (hpoint q.hi))
  exact hlist.trans (by simpa only [pow_two] using
    (Nat.mul_le_mul_right (2 * radius / g + 2) (hpoint q.lo)))

end EditApproximation

end OAI
