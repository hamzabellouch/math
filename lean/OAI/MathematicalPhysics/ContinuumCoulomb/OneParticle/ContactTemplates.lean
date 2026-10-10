import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace OAI

/-! The two fixed nine-link contact templates used after spin subdivision.
Coordinates use the Euclidean plane. The link lengths and separation
bounds are stable under small movements of the sites. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

abbrev ContactPoint := EuclideanSpace ℝ (Fin 2)

def contactPoint (x y : ℝ) : ContactPoint := WithLp.toLp 2 ![x, y]

@[simp] theorem contactPoint_zero (x y : ℝ) : contactPoint x y 0 = x := rfl
@[simp] theorem contactPoint_one (x y : ℝ) : contactPoint x y 1 = y := rfl

theorem contactPoint_dist_sq (x y x' y' : ℝ) :
    dist (contactPoint x y) (contactPoint x' y') ^ 2 =
      (x - x') ^ 2 + (y - y') ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_two, contactPoint_zero, contactPoint_one, Real.dist_eq, sq_abs]

def contactSlopeHeight (c : ℝ) : ℝ := Real.sqrt (1 - c ^ 2)

def contactStepX (c : ℝ) (k : ℕ) : ℝ :=
  if k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6 then c else 1

def contactStepY (c : ℝ) (k : ℕ) : ℝ :=
  if k = 2 ∨ k = 3 then contactSlopeHeight c
  else if k = 5 ∨ k = 6 then -contactSlopeHeight c else 0

def contactPathVertex (c : ℝ) (k : ℕ) : ContactPoint :=
  contactPoint (∑ j ∈ Finset.range k, contactStepX c j)
    (∑ j ∈ Finset.range k, contactStepY c j)

theorem contactSlopeHeight_sq {c : ℝ} (hc : -1 ≤ c) (hc' : c ≤ 1) :
    contactSlopeHeight c ^ 2 = 1 - c ^ 2 := by
  apply Real.sq_sqrt
  nlinarith

theorem contactPathVertex_start (c : ℝ) : contactPathVertex c 0 = contactPoint 0 0 := by
  simp [contactPathVertex]

theorem contactPathVertex_end (c : ℝ) :
    contactPathVertex c 9 = contactPoint (5 + 4 * c) 0 := by
  ext i
  fin_cases i
  · norm_num [contactPathVertex, contactPoint, Finset.sum_range_succ, contactStepX]
    ring
  · norm_num [contactPathVertex, contactPoint, Finset.sum_range_succ, contactStepY]

/-- Every specified link of either template has length exactly one. -/
theorem contactPath_link_length {c : ℝ} (hc : -1 ≤ c) (hc' : c ≤ 1) (k : ℕ) :
    dist (contactPathVertex c (k + 1)) (contactPathVertex c k) = 1 := by
  have hs := contactSlopeHeight_sq hc hc'
  have hsq : dist (contactPathVertex c (k + 1)) (contactPathVertex c k) ^ 2 = 1 := by
    unfold contactPathVertex
    rw [contactPoint_dist_sq]
    simp only [Finset.sum_range_succ, add_sub_cancel_left]
    unfold contactStepX contactStepY
    split_ifs <;> (try omega) <;> nlinarith
  nlinarith [show 0 ≤ dist (contactPathVertex c (k + 1)) (contactPathVertex c k) from dist_nonneg]

theorem contactStepX_lower {c : ℝ} (hc : c ≤ 1) (k : ℕ) : c ≤ contactStepX c k := by
  unfold contactStepX
  split_ifs <;> linarith

/-- Horizontal projection accumulates a uniform positive amount per step. -/
theorem contactPath_horizontal_lower {c : ℝ} (hc : c ≤ 1) {i j : ℕ} (hij : i ≤ j) :
    c * (j - i : ℕ) ≤ contactPathVertex c j 0 - contactPathVertex c i 0 := by
  change c * (j - i : ℕ) ≤ (∑ k ∈ Finset.range j, contactStepX c k) -
    ∑ k ∈ Finset.range i, contactStepX c k
  rw [← Finset.sum_Ico_eq_sub _ hij]
  calc
    c * (j - i : ℕ) = ∑ _k ∈ Finset.Ico i j, c := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun k _ => contactStepX_lower hc k)

/-- Nonconsecutive vertices on a backbone are separated by at least 1.5. -/
theorem contactPath_nonlink_separation {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 1)
    {i j : ℕ} (hij : i + 2 ≤ j) :
    3 / 2 ≤ dist (contactPathVertex c j) (contactPathVertex c i) := by
  have h := contactPath_horizontal_lower hc' (show i ≤ j by omega)
  have hcount : (2 : ℝ) ≤ (j - i : ℕ) := by exact_mod_cast (show 2 ≤ j - i by omega)
  have hx : 3 / 2 ≤ contactPathVertex c j 0 - contactPathVertex c i 0 := by
    nlinarith
  have hdist := contactPoint_dist_sq
    (∑ k ∈ Finset.range j, contactStepX c k) (∑ k ∈ Finset.range j, contactStepY c k)
    (∑ k ∈ Finset.range i, contactStepX c k) (∑ k ∈ Finset.range i, contactStepY c k)
  change dist (contactPathVertex c j) (contactPathVertex c i) ^ 2 =
    (contactPathVertex c j 0 - contactPathVertex c i 0) ^ 2 +
    (contactPathVertex c j 1 - contactPathVertex c i 1) ^ 2 at hdist
  nlinarith [sq_nonneg (contactPathVertex c j 1 - contactPathVertex c i 1),
    show 0 ≤ dist (contactPathVertex c j) (contactPathVertex c i) from dist_nonneg]

theorem contactTemplate_span_eight : contactPathVertex (3 / 4) 9 = contactPoint 8 0 := by
  rw [contactPathVertex_end]
  norm_num

theorem contactTemplate_span_eight_half :
    contactPathVertex (7 / 8) 9 = contactPoint (17 / 2) 0 := by
  rw [contactPathVertex_end]
  norm_num

/-- The paper's nonlink margin survives independent small movements. -/
theorem contact_separation_stable (x y x' y' : ContactPoint)
    (hsep : 7 / 5 ≤ dist x y) (hx : dist x x' ≤ 1 / 20) (hy : dist y y' ≤ 1 / 20) :
    6 / 5 < dist x' y' := by
  have h := dist_triangle x x' y
  have h' := dist_triangle x' y' y
  rw [dist_comm y' y] at h'
  linarith

end ContinuumCoulomb

end

end OAI
