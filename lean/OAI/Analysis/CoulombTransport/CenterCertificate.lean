import OAI.Analysis.CoulombTransport.Model

namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem356.CenterCertificate

/-- The center and the two opposite pairs used in the local construction. -/
def point : Fin 5 → E3 :=
  ![0, !₂[1, 0, 0], !₂[-1, 0, 0], !₂[0, 1, 0], !₂[0, -1, 0]]

theorem point_injective : Function.Injective point := by
  intro i j h
  have h0 := congrArg (fun x : E3 => x 0) h
  have h1 := congrArg (fun x : E3 => x 1) h
  clear h
  fin_cases i <;> fin_cases j
  all_goals norm_num [point] at h0
  all_goals norm_num [point] at h1
  all_goals rfl

/-- The prescribed value of the supporting potential at each center. -/
def potential (i : Fin 5) : ℝ≥0∞ := if i = 0 then 5 / 2 else 0

/-- A center triple belongs to one of the two intended contact families. -/
def Good (i j k : Fin 5) : Prop :=
  ({i, j, k} : Finset (Fin 5)) = {0, 1, 2} ∨
    ({i, j, k} : Finset (Fin 5)) = {0, 3, 4}

/-- The finite-set characterization matches permutation of a canonical branch. -/
theorem good_iff_perm (i j k : Fin 5) :
    Good i j k ↔
      List.Perm [i, j, k] [0, 1, 2] ∨ List.Perm [i, j, k] [0, 3, 4] := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> unfold Good <;> decide

/-- Point-valued permutation form of the good-type condition. -/
theorem perm_points_of_good (i j k : Fin 5) (h : Good i j k) :
    List.Perm [point i, point j, point k] [point 0, point 1, point 2] ∨
      List.Perm [point i, point j, point k] [point 0, point 3, point 4] := by
  rcases (good_iff_perm i j k).1 h with h | h
  · exact Or.inl (by simpa using h.map point)
  · exact Or.inr (by simpa using h.map point)

/-- The pairwise distances of the five centers. -/
def distance (i j : Fin 5) : ℝ :=
  if i = j then 0 else
  if i = 0 ∨ j = 0 then 1 else
  if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) then 2 else Real.sqrt 2

theorem norm_sub_point (i j : Fin 5) : ‖point i - point j‖ = distance i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [point, distance, EuclideanSpace.norm_eq, Fin.sum_univ_succ, Fin.ext_iff]

theorem invDistance_point (i j : Fin 5) :
    invDistance (point i) (point j) = (ENNReal.ofReal (distance i j))⁻¹ := by
  rw [invDistance, norm_sub_point]

theorem cross_pair_gap :
    (5 / 2 : ℝ≥0∞) < 2 + (ENNReal.ofReal (Real.sqrt 2))⁻¹ := by
  have hs : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hsE : ENNReal.ofReal (Real.sqrt 2) < (2 : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_ofNat] using
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg (2 : ℝ))).2 hs
  calc
    (5 / 2 : ℝ≥0∞) = 2 + (2 : ℝ≥0∞)⁻¹ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add]
    _ < 2 + (ENNReal.ofReal (Real.sqrt 2))⁻¹ :=
      ENNReal.add_lt_add_left (by norm_num) (ENNReal.inv_lt_inv.2 hsE)

theorem supporting_inequality (i j k : Fin 5) :
    potential i + potential j + potential k ≤
      coulombCost (point i, (point j, point k)) := by
  have hgap := cross_pair_gap.le
  have harith : (5 / 2 : ℝ≥0∞) = 2 + 2⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]
  have hgap' : (5 / 2 : ℝ≥0∞) ≤ 1 + (1 + (ENNReal.ofReal (Real.sqrt 2))⁻¹) := by
    simpa only [← add_assoc, one_add_one_eq_two] using hgap
  have harith' : (5 / 2 : ℝ≥0∞) = 1 + (1 + (2 : ℝ≥0∞)⁻¹) := by
    simpa only [← add_assoc, one_add_one_eq_two] using harith
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [potential, coulombCost, tripleFst, tripleSnd, tripleThd,
      invDistance_point, distance, Fin.ext_iff]
  all_goals first
    | exact hgap
    | exact harith.le
    | simpa only [add_comm, add_left_comm, add_assoc] using hgap'
    | simpa only [add_comm, add_left_comm, add_assoc] using harith'.le

/-- Every undesired component type has a strict supporting gap at its centers. -/
theorem strict_of_not_good (i j k : Fin 5) (h : ¬ Good i j k) :
    potential i + potential j + potential k <
      coulombCost (point i, (point j, point k)) := by
  have hgap := cross_pair_gap
  have hgap' : (5 / 2 : ℝ≥0∞) < 1 + (1 + (ENNReal.ofReal (Real.sqrt 2))⁻¹) := by
    simpa only [← add_assoc, one_add_one_eq_two] using hgap
  have hpos : 0 < (ENNReal.ofReal (Real.sqrt 2))⁻¹ := ENNReal.inv_pos.2 (by simp)
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals try exact False.elim (h (by unfold Good; decide))
  all_goals norm_num [potential, coulombCost, tripleFst, tripleSnd, tripleThd,
      invDistance_point, distance, Fin.ext_iff]
  all_goals first
    | exact hgap
    | simpa only [add_comm, add_left_comm, add_assoc] using hgap'
    | positivity
    | finiteness

/-- Both intended contact types attain equality at the centers. -/
theorem equality_of_good (i j k : Fin 5) (h : Good i j k) :
    coulombCost (point i, (point j, point k)) =
      potential i + potential j + potential k := by
  have harith : (2 + (2 : ℝ≥0∞)⁻¹) = 5 / 2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]
  have harith' : 1 + (1 + (2 : ℝ≥0∞)⁻¹) = 5 / 2 := by
    simpa only [← add_assoc, one_add_one_eq_two] using harith
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals try (exfalso; revert h; unfold Good; decide)
  all_goals norm_num [potential, coulombCost, tripleFst, tripleSnd, tripleThd,
      invDistance_point, distance, Fin.ext_iff]
  all_goals first
    | exact harith
    | simpa only [add_comm, add_left_comm, add_assoc] using harith'

/-- The five-center supporting certificate has exactly the desired equality types. -/
theorem equality_iff_good (i j k : Fin 5) :
    coulombCost (point i, (point j, point k)) =
      potential i + potential j + potential k ↔ Good i j k := by
  constructor
  · intro h
    by_contra hn
    exact (strict_of_not_good i j k hn).ne h.symm
  · exact equality_of_good i j k

end Problem356.CenterCertificate

end

end OAI
