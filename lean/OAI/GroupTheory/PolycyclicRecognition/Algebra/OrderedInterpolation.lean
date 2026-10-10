import OAI.GroupTheory.PolycyclicRecognition.Geometry.ControlledContraction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MassFractionBounds

namespace OAI

/-! # Ordered interpolation of finitely many nonnegative masses

Zero masses can be omitted. Thus one fixed order on the net gives compatible
interpolations on different finite supports without a simplicial-complex API.
-/

noncomputable section
namespace PolycyclicRecognition

variable {I G : Type*} [MetricSpace G]

def listMass (a : I → ℝ) : List I → ℝ
  | [] => 0
  | i :: l => a i + listMass a l

def listVariation (a b : I → ℝ) (l : List I) : ℝ :=
  listMass (fun i => |a i - b i|) l

def orderedCenter (c : ControlledContraction G) (p₀ : G) (v : I → G) (a : I → ℝ) : List I → G
  | [] => p₀
  | i :: l => c.contract (v i) (listMass a l / listMass a (i :: l)) (orderedCenter c p₀ v a l)

theorem listMass_nonneg (a : I → ℝ) (l : List I) (ha : ∀ i ∈ l, 0 ≤ a i) :
    0 ≤ listMass a l := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih => exact add_nonneg (ha i (by simp)) (ih (fun j hj => ha j (by simp [hj])))

theorem listVariation_nonneg (a b : I → ℝ) (l : List I) : 0 ≤ listVariation a b l :=
  listMass_nonneg _ _ (fun _i _ => abs_nonneg _)

theorem abs_listMass_sub_le (a b : I → ℝ) (l : List I) :
    |listMass a l - listMass b l| ≤ listVariation a b l := by
  induction l with
  | nil => simp [listMass, listVariation]
  | cons i l ih =>
    change |(a i + listMass a l) - (b i + listMass b l)| ≤ |a i - b i| + listVariation a b l
    calc
      _ = |(a i - b i) + (listMass a l - listMass b l)| := by congr 1; ring
      _ ≤ |a i - b i| + |listMass a l - listMass b l| := abs_add_le _ _
      _ ≤ _ := add_le_add le_rfl ih

theorem listMass_filter_zero (a : I → ℝ) (l : List I) :
    listMass a (l.filter (fun i => a i ≠ 0)) = listMass a l := by
  classical
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : a i = 0
    · have hd : decide (a i ≠ 0) = false := by simp only [hi, ne_eq, not_true_eq_false, decide_false]
      rw [List.filter_cons_of_neg (by rw [hd]; decide)]
      simpa only [listMass, hi, zero_add] using ih
    · have hd : decide (a i ≠ 0) = true := by exact decide_eq_true hi
      rw [List.filter_cons_of_pos (p := fun j : I => decide (a j ≠ 0)) (a := i) hd]
      simp only [listMass, ih]

theorem orderedCenter_singleton (c : ControlledContraction G) (p₀ : G)
    (v : I → G) (a : I → ℝ) (i : I) : orderedCenter c p₀ v a [i] = v i := by
  simp [orderedCenter, listMass, c.zero]

/-- Inserting a zero mass at the front does not change a positive-mass
interpolation. This is the compatibility needed at a support boundary. -/
theorem orderedCenter_zero_cons (c : ControlledContraction G) (p₀ : G)
    (v : I → G) (a : I → ℝ) (i : I) (l : List I)
    (hi : a i = 0) (hl : listMass a l ≠ 0) :
    orderedCenter c p₀ v a (i :: l) = orderedCenter c p₀ v a l := by
  simp [orderedCenter, listMass, hi, div_self hl, c.one]

/-- Erasing all zero coordinates does not change the interpolated point
when the total mass is positive. -/
theorem orderedCenter_filter_zero (c : ControlledContraction G) (p₀ : G)
    (v : I → G) (a : I → ℝ) (l : List I)
    (ha : ∀ i ∈ l, 0 ≤ a i) (hm : 0 < listMass a l) :
    orderedCenter c p₀ v a (l.filter (fun i => a i ≠ 0)) = orderedCenter c p₀ v a l := by
  classical
  induction l with
  | nil => simp [listMass] at hm
  | cons i l ih =>
    have hal : ∀ j ∈ l, 0 ≤ a j := fun j hj => ha j (by simp [hj])
    have hml := listMass_nonneg a l hal
    by_cases hi : a i = 0
    · have hpos : 0 < listMass a l := by simpa [listMass, hi] using hm
      have hd : decide (a i ≠ 0) = false := by simp only [hi, ne_eq, not_true_eq_false, decide_false]
      rw [List.filter_cons_of_neg (by rw [hd]; decide), orderedCenter_zero_cons c p₀ v a i l hi hpos.ne']
      exact ih hal hpos
    · have hd : decide (a i ≠ 0) = true := decide_eq_true hi
      rw [List.filter_cons_of_pos (p := fun j : I => decide (a j ≠ 0)) (a := i) hd]
      change c.contract (v i) (listMass a (l.filter (fun j => decide (a j ≠ 0))) /
          listMass a (i :: l.filter (fun j => decide (a j ≠ 0))))
          (orderedCenter c p₀ v a (l.filter (fun j => decide (a j ≠ 0)))) = _
      rw [listMass, listMass_filter_zero]
      by_cases hl : listMass a l = 0
      · simp [hl, orderedCenter, listMass, c.zero]
      · rw [ih hal (lt_of_le_of_ne hml (Ne.symm hl))]
        rfl

end PolycyclicRecognition

end

end OAI
