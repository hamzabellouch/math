import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsNominal
import OAI.NumberTheory.Ostmann.Construction.NominalTotals

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryProductWindows
open Construction InitialCoordinatesTemplate

theorem inheritedCenter_nominal_error (b k l : ℕ) (tb J : ℝ) (w center : ℕ → ℝ)
    (ht : |(∑h,∑i,topCenters b center h i)-(J-2*tb)| ≤ 2)
    (hc : ∀j<k,|typeCenter b j center-w j| ≤ 2) :
    |2*tb+inheritedCenter b k l center-(J+∑j∈Finset.Ico (l+1) k,w j)| ≤ 2+2*(k:ℝ) := by
  rw [inheritedCenter_eq_arrays]
  have he := (Finset.abs_sum_le_sum_abs (s := Finset.Ico (l+1) k) (f := fun j => typeCenter b j center-w j)).trans
    (Finset.sum_le_sum (fun j hj => hc j (Finset.mem_Ico.mp hj).2))
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico] at he
  have hk : ((k-(l+1):ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.sub_le k (l+1)
  have hid : 2*tb+((∑h,∑i,topCenters b center h i)+∑j∈Finset.Ico (l+1) k,typeCenter b j center)-
      (J+∑j∈Finset.Ico (l+1) k,w j) =
    ((∑h,∑i,topCenters b center h i)-(J-2*tb)) +
      ∑j∈Finset.Ico (l+1) k,(typeCenter b j center-w j) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith)

theorem removedCenter_nominal_error (b k l : ℕ) (hl : l<k) (w center : ℕ → ℝ)
    (hc : ∀j<k,|typeCenter b j center-w j| ≤ 2) :
    |removedCenter b k l center-w l| ≤ 2 := by
  rw [removedCenter_eq_typeCenter b k l hl]
  exact hc l hl

def nominalInheritedWidth (k l : ℕ) : ℝ := 1+(2:ℝ)^l*(10+6*(k:ℝ))
def nominalRemovedWidth (k l : ℕ) : ℝ := (2:ℝ)^l*(8+4*(k:ℝ))

theorem inherited_window_normalize (b k l : ℕ) (logH G tb J Δ : ℝ) (w center : ℕ → ℝ)
    (hH : |logH-(G+(2:ℝ)^l*(2*tb+inheritedCenter b k l center))| ≤ inheritedWidth k l)
    (ht : |(∑h,∑i,topCenters b center h i)-(J-2*tb)| ≤ 2)
    (hc : ∀j<k,|typeCenter b j center-w j| ≤ 2)
    (hw : (2:ℝ)^l*(J+∑j∈Finset.Ico (l+1) k,w j) = (2:ℝ)^l*w l+Δ) :
    |logH-(G+(2:ℝ)^l*w l+Δ)| ≤ nominalInheritedWidth k l := by
  have hC := inheritedCenter_nominal_error b k l tb J w center ht hc
  have hr : 0 ≤ (2:ℝ)^l := by positivity
  have he := mul_le_mul_of_nonneg_left hC hr
  rw [←abs_of_nonneg hr,←abs_mul] at he
  rw [abs_of_nonneg hr] at he
  have hid : logH-(G+(2:ℝ)^l*w l+Δ) =
      (logH-(G+(2:ℝ)^l*(2*tb+inheritedCenter b k l center))) +
        (2:ℝ)^l*(2*tb+inheritedCenter b k l center-(J+∑j∈Finset.Ico (l+1) k,w j)) := by
    rw [mul_sub,hw]
    ring
  rw [hid]
  have ha := (abs_add_le _ _).trans (add_le_add hH he)
  convert ha using 1
  unfold nominalInheritedWidth inheritedWidth
  ring

theorem removed_window_normalize (b k l : ℕ) (hl : l<k) (logU : ℝ) (w center : ℕ → ℝ)
    (hU : |logU-(2:ℝ)^l*removedCenter b k l center| ≤ removedWidth k l)
    (hc : ∀j<k,|typeCenter b j center-w j| ≤ 2) :
    |logU-(2:ℝ)^l*w l| ≤ nominalRemovedWidth k l := by
  have he := mul_le_mul_of_nonneg_left (removedCenter_nominal_error b k l hl w center hc)
    (show 0 ≤ (2:ℝ)^l by positivity)
  rw [←abs_of_nonneg (show 0 ≤ (2:ℝ)^l by positivity),←abs_mul] at he
  rw [abs_of_nonneg (show 0 ≤ (2:ℝ)^l by positivity)] at he
  have hid : logU-(2:ℝ)^l*w l = (logU-(2:ℝ)^l*removedCenter b k l center)+
      (2:ℝ)^l*(removedCenter b k l center-w l) := by ring
  rw [hid]
  have ha := (abs_add_le _ _).trans (add_le_add hU he)
  convert ha using 1
  unfold nominalRemovedWidth removedWidth
  ring

end Ostmann.Arithmetic.HistoryProductWindows

end

end OAI
