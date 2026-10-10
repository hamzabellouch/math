import OAI.Combinatorics.Crossing.StepEvents
import Mathlib.Tactic.FieldSimp

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def positiveIndicator (x : ℝ) : ℝ := if 0 < x then 1 else 0

def slopeSign (b : ℝ) : ℝ := if 0 < b then 1 else -1

def sideBefore (b : ℝ) : ℝ := if 0 < b then 0 else 1

def sideAfter (b : ℝ) : ℝ := if 0 < b then 1 else 0

theorem sideAfter_sub_before (b : ℝ) : sideAfter b-sideBefore b = slopeSign b := by
  unfold sideAfter sideBefore slopeSign
  split_ifs <;> norm_num

theorem positiveIndicator_factor (b r t : ℝ) (hb : b ≠ 0) (ht : t ≠ r) :
    positiveIndicator (b*(t-r)) = stepAt r (sideBefore b) (sideAfter b) t := by
  rcases lt_or_gt_of_ne hb with hb | hb
  · by_cases htr : t<r
    · have hprod := mul_pos_of_neg_of_neg hb (sub_neg.mpr htr)
      simp [positiveIndicator,stepAt,sideBefore,htr,hprod,not_lt.mpr hb.le]
    · have hrt : r<t := lt_of_le_of_ne (le_of_not_gt htr) ht.symm
      have hprod := mul_neg_of_neg_of_pos hb (sub_pos.mpr hrt)
      simp [positiveIndicator,stepAt,sideAfter,htr,not_lt.mpr hprod.le,not_lt.mpr hb.le]
  · by_cases htr : t<r
    · have hprod := mul_neg_of_pos_of_neg hb (sub_neg.mpr htr)
      simp [positiveIndicator,stepAt,sideBefore,htr,not_lt.mpr hprod.le,hb]
    · have hrt : r<t := lt_of_le_of_ne (le_of_not_gt htr) ht.symm
      have hprod := mul_pos hb (sub_pos.mpr hrt)
      simp [positiveIndicator,stepAt,sideAfter,htr,hprod,hb]

theorem sum_affine_side_events (n : ℕ) (r b : Fin n → ℝ)
    (hr : StrictMono r) (hb : ∀ i, b i ≠ 0) (h0 : ∀ i, r i ≠ 0) (h1 : ∀ i, r i ≠ 1) :
    (∑ i, if 0<r i ∧ r i<1 then slopeSign (b i) *
      (∏ j, if j=i then 1 else positiveIndicator (b j*(r i-r j))) else 0) =
      (∏ i, positiveIndicator (b i*(1-r i))) - ∏ i, positiveIndicator (b i*(0-r i)) := by
  have hh := sum_stepEvent n r (fun i => sideBefore (b i)) (fun i => sideAfter (b i)) hr h0 h1
  have he : ∀ i : Fin n, stepEvent r (fun i => sideBefore (b i)) (fun i => sideAfter (b i)) i =
      if 0<r i ∧ r i<1 then slopeSign (b i) *
        (∏ j, if j=i then 1 else positiveIndicator (b j*(r i-r j))) else 0 := by
    intro i
    unfold stepEvent
    rw [sideAfter_sub_before]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hji : j=i
    · simp [hji]
    · rw [ite_eq_right hji,ite_eq_right hji]
      exact (positiveIndicator_factor (b j) (r j) (r i) (hb j) (hr.injective.ne (Ne.symm hji))).symm
  simp_rw [he] at hh
  rw [hh]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact (positiveIndicator_factor (b i) (r i) 1 (hb i) (h1 i).symm).symm
  · apply Finset.prod_congr rfl
    intro i hi
    exact (positiveIndicator_factor (b i) (r i) 0 (hb i) (h0 i).symm).symm

end Zarankiewicz

end

end OAI
