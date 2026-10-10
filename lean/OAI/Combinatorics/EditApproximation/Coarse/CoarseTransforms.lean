import OAI.Combinatorics.EditApproximation.Coarse.CoarseEstimator

namespace OAI

/-!
# Linear sweeps for the coarse penalty transform

The finite minima define the semantic arrays. These sweeps compute them
with one rational addition and one comparison per scan transition.
-/

namespace EditApproximation

open Finset

def coarsePrefixMinimum (value : ℕ → ℚ) : ℕ → ℚ
  | 0 => value 0
  | v + 1 => min (value (v + 1)) (coarsePrefixMinimum value v + 2)

theorem coarsePrefixMinimum_le (value : ℕ → ℚ) (v u : ℕ) (hu : u ≤ v) :
    coarsePrefixMinimum value v ≤ value u + 2 * (v - u : ℕ) := by
  induction v with
  | zero =>
    have hu0 : u = 0 := by omega
    subst u
    simp [coarsePrefixMinimum]
  | succ v ih =>
    by_cases hequal : u = v + 1
    · subst u
      simpa only [coarsePrefixMinimum, Nat.sub_self, Nat.cast_zero, mul_zero, add_zero] using
        (min_le_left (value (v + 1)) (coarsePrefixMinimum value v + 2))
    · have hule : u ≤ v := by omega
      have hdiff : v + 1 - u = (v - u) + 1 := by omega
      calc
        _ ≤ coarsePrefixMinimum value v + 2 := min_le_right _ _
        _ ≤ value u + 2 * (v - u : ℕ) + 2 := by linarith [ih hule]
        _ = _ := by rw [hdiff]; push_cast; ring

theorem coarsePrefixMinimum_attained (value : ℕ → ℚ) (v : ℕ) :
    ∃ u ≤ v, coarsePrefixMinimum value v = value u + 2 * (v - u : ℕ) := by
  induction v with
  | zero => exact ⟨0, le_rfl, by simp [coarsePrefixMinimum]⟩
  | succ v ih =>
    by_cases hnew : value (v + 1) ≤ coarsePrefixMinimum value v + 2
    · exact ⟨v + 1, le_rfl, by simp only [coarsePrefixMinimum, min_eq_left hnew,
        Nat.sub_self, Nat.cast_zero, mul_zero, add_zero]⟩
    · obtain ⟨u, hu, hequal⟩ := ih
      refine ⟨u, by omega, ?_⟩
      rw [coarsePrefixMinimum, min_eq_right (le_of_not_ge hnew), hequal]
      have hdiff : v + 1 - u = (v - u) + 1 := by omega
      rw [hdiff]
      push_cast
      ring

/-- The executable left sweep; Lean's `scanl` traverses its input once. -/
def coarseLeftSweep : List ℚ → List ℚ
  | [] => []
  | first :: rest => rest.scanl (fun previous value => min value (previous + 2)) first

theorem coarseLeftSweep_length (source : List ℚ) :
    (coarseLeftSweep source).length = source.length := by
  cases source <;> simp only [coarseLeftSweep, List.length_nil, List.length_cons, List.length_scanl]

theorem coarseLeftSweep_getElem (source : List ℚ) (v : ℕ) (hv : v < source.length) :
    (coarseLeftSweep source)[v]'(by rw [coarseLeftSweep_length]; exact hv) =
      coarsePrefixMinimum (fun i => source[i]?.getD 0) v := by
  cases source with
  | nil => simp at hv
  | cons first rest =>
    induction v with
    | zero => simp only [coarseLeftSweep, List.getElem_scanl_zero, coarsePrefixMinimum,
        List.getElem?_cons_zero, Option.getD_some]
    | succ v ih =>
      simp only [coarseLeftSweep]
      rw [List.getElem_succ_scanl]
      rw [coarsePrefixMinimum]
      have hvprev : v < (first :: rest).length := by simp only [List.length_cons] at hv ⊢; omega
      have hprevious := ih hvprev
      simp only [coarseLeftSweep] at hprevious
      rw [hprevious]
      have hrestIndex : v < rest.length := by simp only [List.length_cons] at hv; omega
      simp only [List.getElem?_cons_succ]
      rw [List.getElem?_eq_getElem hrestIndex, Option.getD_some]

/-- A costed scan records the addition and comparison actually performed
at each transition; list traversal is charged separately by the RAM model. -/
def coarseCostedScan (previous : ℚ) : List ℚ → List ℚ × ℕ
  | [] => ([previous], 0)
  | value :: rest =>
    let next := min value (previous + 2)
    let result := coarseCostedScan next rest
    (previous :: result.1, result.2 + 2)

theorem coarseCostedScan_result (previous : ℚ) (source : List ℚ) :
    (coarseCostedScan previous source).1 =
      source.scanl (fun previous value => min value (previous + 2)) previous ∧
    (coarseCostedScan previous source).2 = 2 * source.length := by
  induction source generalizing previous with
  | nil => simp [coarseCostedScan]
  | cons value rest ih =>
    have hnext := ih (min value (previous + 2))
    simp only [coarseCostedScan, List.scanl_cons, List.length_cons, hnext.1, hnext.2]
    exact ⟨trivial, by omega⟩

def coarseArrayLookup {n : ℕ} (value : Fin n → ℚ) (i : ℕ) : ℚ :=
  if h : i < n then value ⟨i, h⟩ else 0

def coarseReverseLookup {n : ℕ} (value : Fin n → ℚ) (i : ℕ) : ℚ :=
  if h : i < n then value ⟨n - 1 - i, by omega⟩ else 0

/-- Two one-sided recurrences equal the complete literal penalty minimum. -/
theorem coarse_two_prefix_minimum {n : ℕ} [NeZero n] (value : Fin n → ℚ) (v : Fin n) :
    min (coarsePrefixMinimum (coarseArrayLookup value) v.val)
        (coarsePrefixMinimum (coarseReverseLookup value) (n - 1 - v.val)) =
      univ.inf' univ_nonempty (fun u => value u + (2 * Nat.dist v.val u.val : ℕ)) := by
  apply le_antisymm
  · apply le_inf'
    intro u hu
    by_cases hleft : u.val ≤ v.val
    · have hprefix := coarsePrefixMinimum_le (coarseArrayLookup value) v.val u.val hleft
      have hdistance := Nat.dist_eq_sub_of_le_right hleft
      apply (min_le_left _ _).trans
      simpa only [coarseArrayLookup, dite_eq_left u.isLt, Nat.cast_mul, Nat.cast_ofNat,
        hdistance] using hprefix
    · have hright : v.val ≤ u.val := by omega
      have hindex : n - 1 - u.val ≤ n - 1 - v.val := by omega
      have hun : n - 1 - u.val < n := by have := u.isLt; omega
      have hprefix := coarsePrefixMinimum_le (coarseReverseLookup value)
        (n - 1 - v.val) (n - 1 - u.val) hindex
      have hdouble : (⟨n - 1 - (n - 1 - u.val), by omega⟩ : Fin n) = u := by
        apply Fin.ext
        change n - 1 - (n - 1 - u.val) = u.val
        have := u.isLt
        omega
      have hgap : n - 1 - v.val - (n - 1 - u.val) = u.val - v.val := by
        have := u.isLt
        have := v.isLt
        omega
      apply (min_le_right _ _).trans
      simpa only [coarseReverseLookup, dite_eq_left hun, hdouble, hgap,
        Nat.dist_eq_sub_of_le hright, Nat.cast_mul, Nat.cast_ofNat] using hprefix
  · apply le_min
    · obtain ⟨u, hu, hequal⟩ := coarsePrefixMinimum_attained (coarseArrayLookup value) v.val
      have hun : u < n := lt_of_le_of_lt hu v.isLt
      have hminimum := inf'_le (fun u => value u + (2 * Nat.dist v.val u.val : ℕ))
        (mem_univ (⟨u, hun⟩ : Fin n))
      rw [hequal]
      simpa only [coarseArrayLookup, dite_eq_left hun, Nat.dist_eq_sub_of_le_right hu,
        Nat.cast_mul, Nat.cast_ofNat] using hminimum
    · obtain ⟨u, hu, hequal⟩ := coarsePrefixMinimum_attained
        (coarseReverseLookup value) (n - 1 - v.val)
      have hun : u < n := by have := v.isLt; omega
      let next : Fin n := ⟨n - 1 - u, by omega⟩
      have hright : v.val ≤ next.val := by dsimp [next]; have := v.isLt; omega
      have hgap : n - 1 - v.val - u = next.val - v.val := by
        dsimp [next]
        have := v.isLt
        omega
      have hminimum := inf'_le (fun u => value u + (2 * Nat.dist v.val u.val : ℕ)) (mem_univ next)
      rw [hequal]
      simpa only [coarseReverseLookup, dite_eq_left hun, Nat.dist_eq_sub_of_le hright,
        hgap, Nat.cast_mul, Nat.cast_ofNat] using hminimum

/-- Literal array output of the two linear sweeps. -/
def coarsePenaltyTransform (source : List ℚ) : List ℚ :=
  List.zipWith min (coarseLeftSweep source) (coarseLeftSweep source.reverse).reverse

theorem coarsePenaltyTransform_length (source : List ℚ) :
    (coarsePenaltyTransform source).length = source.length := by
  simp only [coarsePenaltyTransform, List.length_zipWith, List.length_reverse,
    coarseLeftSweep_length, min_self]

theorem coarseArrayLookup_list (source : List ℚ) :
    coarseArrayLookup (fun i : Fin source.length => source[i.val]) =
      fun i => source[i]?.getD 0 := by
  funext i
  by_cases hi : i < source.length
  · simp only [coarseArrayLookup, dite_eq_left hi, List.getElem?_eq_getElem hi, Option.getD_some]
  · have hge : source.length ≤ i := by omega
    simp only [coarseArrayLookup, dite_eq_right hi, List.getElem?_eq_none hge, Option.getD_none]

theorem coarseReverseLookup_list (source : List ℚ) :
    coarseReverseLookup (fun i : Fin source.length => source[i.val]) =
      fun i => source.reverse[i]?.getD 0 := by
  funext i
  by_cases hi : i < source.length
  · have hir : i < source.reverse.length := by simpa only [List.length_reverse] using hi
    simp only [coarseReverseLookup, dite_eq_left hi, List.getElem?_eq_getElem hir,
      Option.getD_some, List.getElem_reverse]
  · have hir : source.reverse.length ≤ i := by simp only [List.length_reverse]; omega
    simp only [coarseReverseLookup, dite_eq_right hi, List.getElem?_eq_none hir, Option.getD_none]

/-- Every returned array cell equals the complete finite semantic minimum. -/
theorem coarsePenaltyTransform_getElem (source : List ℚ) [NeZero source.length]
    (v : Fin source.length) :
    (coarsePenaltyTransform source)[v.val]'(by rw [coarsePenaltyTransform_length]; exact v.isLt) =
      univ.inf' univ_nonempty (fun u : Fin source.length =>
        source[u.val] + (2 * Nat.dist v.val u.val : ℕ)) := by
  have hreverse : source.length - 1 - v.val < source.reverse.length := by
    simp only [List.length_reverse]
    have := v.isLt
    omega
  simp only [coarsePenaltyTransform]
  rw [List.getElem_zipWith, List.getElem_reverse]
  simp only [coarseLeftSweep_length, List.length_reverse]
  rw [coarseLeftSweep_getElem source v.val v.isLt,
    coarseLeftSweep_getElem source.reverse (source.length - 1 - v.val) hreverse]
  rw [← coarseArrayLookup_list, ← coarseReverseLookup_list]
  exact coarse_two_prefix_minimum (fun i => source[i.val]) v

def coarseCostedLeftSweep : List ℚ → List ℚ × ℕ
  | [] => ([], 0)
  | first :: rest => coarseCostedScan first rest

theorem coarseCostedLeftSweep_result (source : List ℚ) :
    (coarseCostedLeftSweep source).1 = coarseLeftSweep source ∧
      (coarseCostedLeftSweep source).2 = 2 * (source.length - 1) := by
  cases source with
  | nil => simp [coarseCostedLeftSweep, coarseLeftSweep]
  | cons first rest =>
    simpa only [coarseCostedLeftSweep, coarseLeftSweep, List.length_cons,
      Nat.add_sub_cancel] using coarseCostedScan_result first rest

/-- Instrumented actual sweeps plus the final cellwise comparisons. -/
def coarseCostedPenaltyTransform (source : List ℚ) : List ℚ × ℕ :=
  let left := coarseCostedLeftSweep source
  let right := coarseCostedLeftSweep source.reverse
  (List.zipWith min left.1 right.1.reverse,
    left.2 + right.2 + min left.1.length right.1.length)

theorem coarseCostedPenaltyTransform_result (source : List ℚ) :
    (coarseCostedPenaltyTransform source).1 = coarsePenaltyTransform source ∧
      (coarseCostedPenaltyTransform source).2 ≤ 5 * source.length := by
  have hleft := coarseCostedLeftSweep_result source
  have hright := coarseCostedLeftSweep_result source.reverse
  simp only [coarseCostedPenaltyTransform, coarsePenaltyTransform, hleft.1, hright.1,
    hleft.2, hright.2, coarseLeftSweep_length, List.length_reverse, min_self]
  exact ⟨trivial, by omega⟩

end EditApproximation

end OAI
